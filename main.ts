import { score } from './score';
import { component_render } from './component';
import { find_note_at_mpoint, find_note_index_at_mpoint, xd_of_ticksd } from './roll';
import { RollMouseState, MouseAction, Action, AppState, BaseState, Note, mpoint, Mode, Score,
			initialState, Pattern } from './types';
import { keyOf } from './key';
import { Immutable as Im, get, set, update, getIn, setIn, updateIn, fromJS, toJS } from './immutable';
import { play } from './audio';

declare const debug_glob: any;

const notes = score.patterns['default'].notes;
notes.forEach(note => note.pitch += 12);

window.onload = () => {
  document.onkeydown = (e) => dispatch({t: "Key", key: keyOf(e)});
  document.onmouseup = (e) => dispatch({t: "Mouseup"});
  render();
}

// Picked up this notion from
// http://stackoverflow.com/questions/39419170/how-do-i-check-that-a-switch-block-is-exhaustive-in-typescript
// not sure if there's a better way of doing it.
export function unreachable(x: never): never {
  throw new Error("Shouldn't get here.");
}

let state: Im<AppState> = set(initialState, 'score', fromJS(score));


// snap to grid
function snap(gridSize: number, noteSize: number, mp: mpoint): Note {
  const gs = gridSize;
  const b = Math.floor(mp.time / gs) * gs;
  return {pitch: mp.pitch, time: [b, b + noteSize]};
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

// just not memoized right now
function memoized<T, V, W>(select: (x: T) => V, view: (y: V) => W): (x: T) => W {
  return x => view(select(x));
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
  switch(ms.t) {
  case "hover":
	 switch(a.t) {
	 case "Mousemove": return {t: "hover", mp: a.mpoint};
	 case "Mousedown": return {t: "down", orig: a.mpoint, now: a.mpoint};
	 case "Mouseup": return ms; // this happens for mouse events that started outside the editor
	 case "Mouseleave": return {...ms, mp: null};
	 default: throw unreachable(a);
	 }

  case "down":
	 switch(a.t) {
	 case "Mousemove": {
		const pa: mpoint = ms.orig;
		const pb: mpoint = a.mpoint;
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
	 case "Mousemove": return {...ms, now: a.mpoint};
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

function reduceCmd(state: Im<AppState>, cmd: string): Im<AppState> {
  const words = cmd.split(/ /);
  switch (words[0]) {
  case "clear":
	 return updateCurrentNotes(state, x => fromJS([]));
  case "edit":
	 let st = set(state, 'mode', fromJS({t: 'editPattern', patName: words[1]}));
	 if (currentPatUndefined(st)) {
		st = setCurrentPat(st, {notes: [], length: 32});
	 }
	 return st;
  default: return state;
  }
}

function updateCurrentNotes(state: Im<AppState>, f: (x: Im<Note[]>) => Im<Note[]>): Im<AppState> {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return state; // maybe console.log in this case?
  return updateIn(state, x => x.score.patterns[pat].notes, f);
}

function getCurrentPattern(state: Im<AppState>): string | undefined {
  const mode = toJS<Mode>(get(state, "mode"));
  switch(mode.t) {
  case "editPattern": return mode.patName;
  default: return undefined;
  }
}

function currentPatUndefined(state: Im<AppState>): boolean {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  const p = getIn(state, x => x.score.patterns[pat])
  return p == undefined
}

function _getCurrentNotes(state: Im<AppState>): Note[] | undefined {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  const notes = getIn(state, x => x.score.patterns[pat].notes)
  if (notes == undefined) return undefined; // this is definitely a non-exceptional case
  return toJS(notes);
}

// ad hoc cache, not sure if I should be doing something smarter
let lastState = null;
let lastAnswer = null;
function getCurrentNotes(state: Im<AppState>): Note[] | undefined {
  if (state != lastState) {
    lastState = state; lastAnswer = _getCurrentNotes(lastState);
  }
  return lastAnswer;
}

function setCurrentNotes(state: Im<AppState>, notes: Note[]): Im<AppState> {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  return setIn(state, x => x.score.patterns[pat].notes, fromJS(notes))
}

function getCurrentPat(state: Im<AppState>): Pattern | undefined {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  const p = getIn(state, x => x.score.patterns[pat])
  if (p == undefined) return undefined; // this is definitely a non-exceptional case
  return toJS(p);
}

function setCurrentPat(state: Im<AppState>, p: Pattern): Im<AppState> {
  const pat = getCurrentPattern(state);
  return setIn(state, x => x.score.patterns[pat], fromJS(p))
}

export function reduce(state: Im<AppState>, a: Action): Im<AppState> {
  switch (a.t) {
  case "Mousemove":
  case "Mouseleave":
  case "Mousedown":
  case "Mouseup":
	 const mode = toJS<Mode>(get(state, 'mode'));
	 switch(mode.t) {
	 case "editPattern":
		const nst = rollReduceMouse(state, mode.mouseState, a);
		const nmst = rollNewMouseState(state, mode.mouseState, a);
		return set(nst, 'mode', fromJS<Mode>({...mode, mouseState: nmst}));
	 default: return state;
	 }
  case "Play":
	 play(a.score, v => dispatch({t: "SetCurrentPlaybackTime", v}));
	 return state;

  case "SetCurrentPlaybackTime":
	 return set(state, 'offsetTicks', a.v);

  case "Key": return reduceKey(state, a.key);

  case "Vscroll": return set(state, 'scrollOctave', a.top);

  case "ExecMinibuf":
	 let s = reduceCmd(state, get(state, 'minibuf'));
	 s = set(s, 'minibufferVisible', false);
	 s = set(s, 'minibuf', '');
	 return s;

  case "SetMinibuf":
	 return set(state, 'minibuf', a.v);

  case "EditSong":
	 return set(state, 'mode', fromJS<Mode>({t: "editSong"}));

  case "EditPat":
	 return set(state, 'mode', fromJS<Mode>({t: "editPattern", patName: a.patName,
														  mouseState: {t: "hover", mp: null }}));

  default: unreachable(a);
  }
}

export function reduceConsistent(state: Im<AppState>, a: Action): Im<AppState> {
  const ns = reduce(state, a);
  const mode = toJS<Mode>(get(ns, 'mode'));
  switch(mode.t) {
  case "editPattern":
	 return set(ns, 'previewNote', fromJS(previewNote(ns, mode.mouseState)));
  default:
	 return ns;
  }
}

export function dispatch(a: Action): void {
  state = reduceConsistent(state, a);
  render();
}

function reduceKey(state: Im<AppState>, key: string): Im<AppState> {
  switch(key) {
  case "A-x":
	 return update(state, 'minibufferVisible', x => !x);
  case ",":
	 if (state.minibufferVisible) return state;
	 return update(state, 'gridSize', x => x / 2);
  case ".":
	 if (state.minibufferVisible) return state;
	 return update(state, 'gridSize', x => x * 2);
  default: return state;
  }
}

function render() {
  component_render(toJS(state));
}

// debugging
setTimeout(() => {
  window['score'] = score;
  for (let x in debug_glob) {
	 window[x] = debug_glob[x];
  }
}, 0);
