import { MouseAction, Note, cpoint } from './types';
import { AppState, Mode } from './state';
import { unreachable, snap } from './main';
import { Immutable as Im, get, set, getIn, setIn, fromJS, toJS } from './immutable';
import { getCurrentNotes, updateCurrentNotes, getCurrentPat } from './accessors';
import { SCALE, PITCH_HEIGHT, PIANO_WIDTH, GUTTER_WIDTH, PIXELS_PER_TICK,
			mpoint, RollMouseState, RollMode,
			y0pitch_of_scrollOctave } from './roll-util';

function find_note_at_mpoint(notes: Note[], mp: mpoint): Note | undefined {
  return notes.find(note => {
	 return (note.pitch == mp.pitch
				&& note.time[0] <= mp.time
				&& note.time[1] >= mp.time);
  });
}

function find_note_index_at_mpoint(notes: Note[], mp: mpoint): number {
  return notes.findIndex(note => {
	 return (note.pitch == mp.pitch
				&& note.time[0] <= mp.time
				&& note.time[1] >= mp.time);
  });
}

function mpoint_of_cpoint(cp: cpoint, scrollOctave: number): mpoint {
  return {...cp,
	 pitch: y0pitch_of_scrollOctave(scrollOctave) - Math.floor(cp.y / (SCALE * PITCH_HEIGHT)),
	 time: (cp.x - (PIANO_WIDTH + GUTTER_WIDTH + SCALE)) / PIXELS_PER_TICK,
  };
}

function xd_of_ticksd(ticksd: number): number {
  return ticksd * PIXELS_PER_TICK;
}

// x is a floating point number. We want to return an int, but have
// the function feel reasonably responsive even if x isn't that far
// from zero.
function augment_and_snap(x: number) {
  const sgn = x > 0 ? 1 : -1;
  const abs = Math.abs(x);
  const snap = Math.floor(abs+0.5);
  return snap * sgn;
}

function rollNewMouseState(state: Im<AppState>, ms: RollMouseState, a: MouseAction): RollMouseState {
  const notes = getCurrentNotes(state);
  function m_of_c(x: cpoint) { return mpoint_of_cpoint(x, get(state, 'scrollOctave')); }
  switch(ms.t) {
  case "hover":
	 switch(a.t) {
	 case "Mousemove": return {t: "hover", mp: m_of_c(a.p)};
	 case "Mousedown": const mp = m_of_c(a.p); return {t: "down", orig: mp, now: mp};
	 case "Mouseup": return ms; // this happens for mouse events that started outside the editor
	 case "Mouseleave": return {...ms, mp: null};
	 default: throw unreachable(a);
	 }

  case "down":
	 switch(a.t) {
	 case "Mousemove": {
		const pa: mpoint = ms.orig;
		const pb: mpoint = m_of_c(a.p);
		let rv: RollMouseState = {t: "down", orig: pa, now: pb};
		if (xd_of_ticksd(Math.abs(pa.time - pb.time)) > 5) {
		  const noteIx = find_note_index_at_mpoint(notes, pa);
		  if (noteIx != -1) {
			 const note = notes[noteIx];
			 const fromRight = pa.time > (note.time[0] + note.time[1]) / 2;
			 rv = {t: "resizeNote", fromRight, orig: pa, now: pb, note, noteIx};
		  }
		}
		return rv;
	 }
	 case "Mousedown": throw "impossible";
	 case "Mouseup": return {t: "hover", mp: ms.now};
	 case "Mouseleave": return {...ms, now: null};
	 default: throw unreachable(a);
	 }

  case "resizeNote":
	 switch(a.t) {
	 case "Mousemove": return {...ms, now: m_of_c(a.p)};
	 case "Mousedown": throw "impossible";
	 case "Mouseup": return {t: "hover", mp: ms.now};
	 case "Mouseleave": return {...ms, now: null};
	 default: throw unreachable(a);
	 }
  }
}

// collateral state changes because of mouse actions
function rollReduceMouse(state: Im<AppState>, ms: RollMouseState, a: MouseAction): Im<AppState> {
  const notes = getCurrentNotes(state);

  switch(ms.t) {
  case "down":
	 if (a.t == "Mouseup") {
		const mp = ms.orig;
		const note = find_note_at_mpoint(notes, mp);
		if (note) {
		  // Delete note
		  const notIt = x => JSON.stringify(x) != JSON.stringify(note);
		  const s = updateCurrentNotes(state, n => fromJS(toJS(n).filter(notIt)));
		  return set(s, 'noteSize', note.time[1] - note.time[0]);
		}
		else {
		  // Create note
		  const sn: Note = restrictAtState(snap(get(state, 'gridSize'), get(state, 'noteSize'), mp), state);
		  if (sn == null)
			 return state
		  else
			 return updateCurrentNotes(state, n => fromJS(toJS(n).concat([sn])));
		}
	 }
	 break;
  case "resizeNote":
	 if (a.t == "Mousemove") {
		if (ms.now == null) return state;
		const oldLength = (ms.note.time[1] - ms.note.time[0]);
		const lengthDiff = augment_and_snap(ms.now.time - ms.orig.time);
		if (ms.fromRight) {
		  const newLength = Math.max(1, lengthDiff + oldLength);
		  const pat = getCurrentPat(state);
		  if (pat == undefined)
			 return state;
		  const newEnd = Math.min(pat.length, ms.note.time[0] + newLength);

		  const s = updateCurrentNotes(state, n => setIn(n, x => x[ms.noteIx].time[1], newEnd));
		  return set(s, 'noteSize', newLength);
		}
		else {
		  const newLength = Math.max(1, oldLength - lengthDiff);
		  const newBegin = Math.max(0, ms.note.time[1] - newLength);

		  const s = updateCurrentNotes(state, n => setIn(n, x => x[ms.noteIx].time[0], newBegin));
		  return set(s, 'noteSize', newLength);
		}

	 }
	 break;
  }
  return state;
}

function previewNote(state: Im<AppState>, ms: RollMouseState): Note | null {
  const notes = getCurrentNotes(state);
  const gridSize = get(state, 'gridSize');
  const noteSize = get(state, 'noteSize');
  switch (ms.t) {
  case "hover":
	 const mh = ms.mp;
	 if (mh == null)
		return null;
	 const found = find_note_at_mpoint(notes, mh);
	 if (found) return found;
	 return restrictAtState(snap(gridSize, noteSize, mh), state);
  case "down":
  case "resizeNote":
	 return null;
  default: unreachable(ms);
  }
}

export function rollReduce(state: Im<AppState>, mode: RollMode, a: MouseAction): Im<AppState> {
  const nst = rollReduceMouse(state, mode.mouseState, a);
  const nmst = rollNewMouseState(state, mode.mouseState, a);
  return set(nst, 'mode', fromJS<Mode>({...mode, mouseState: nmst}));
}

export function rollReduceConsistent(state: Im<AppState>, ms: RollMouseState): Im<AppState> {
 return set(state, 'previewNote', fromJS(previewNote(state, ms)));
}

function restrict(note: Note, patlength: number): Note | null {
  if (note.time[0] < 0) return null;
  if (note.time[0] >= patlength) return null;
  if (note.time[1] > patlength) {
	 const newStart = note.time[0] - (note.time[1] - patlength);
	 if (newStart < 0) return null;
	 return {pitch: note.pitch, time: [newStart, patlength]};
  }
  return note;
}

function restrictAtState(note: Note, state: Im<AppState>): Note | null {
  const mode = toJS<Mode>(get(state, 'mode'));
  switch(mode.t) {
  case "editPattern":
	 return restrict(note, getIn(state, x => x.score.patterns[mode.patName].length));
  default: return null;
  }
}
