import { AppState, SongMouseState, Song, SongMode, RollMode,
			MouseAction, Action, mpoint, cpoint, PatUse } from './types';
import { PIXELS_PER_TICK } from './song-editor';
import { Immutable as Im, get, getIn, set, update, setIn, fromJS, toJS } from './immutable';
import { getSong, updateSong } from './accessors';
import { unreachable } from './main';

const DOUBLE_CLICK_SPEED = 300;
const LANE_HEIGHT = 50; // XXX belongs in song-editor.tsx probably

function find_pat_use(song: Song, cp: cpoint): PatUse | undefined {
  const {x, y} = cp;
  return song.find(pu => x >= pu.start * PIXELS_PER_TICK && x <= (pu.start + pu.duration) * PIXELS_PER_TICK &&
		y >= 0 && y <= LANE_HEIGHT);
}

function find_pat_use_index(song: Song, cp: cpoint): number {
  const {x, y} = cp;
  return song.findIndex(pu => x >= pu.start * PIXELS_PER_TICK && x <= (pu.start + pu.duration) * PIXELS_PER_TICK &&
		y >= 0 && y <= LANE_HEIGHT);
}

export function songNewMouseState(state: Im<AppState>, ms: SongMouseState, a: MouseAction): SongMouseState {
  const notes = getSong(state);
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
		let rv: SongMouseState = {t: "down", orig: pa, now: pb};
		if (Math.abs(pa.x - pb.x) > 5) {
		  const patIx = find_pat_use_index(notes, pa);
		  if (patIx != -1) {
			 const song = getSong(state);
			 const patUse = song[patIx];
			 rv = {t: "dragPat", orig: pa, now: pb, patUse, patIx};
		  }
		}
		return rv;
	 }
	 case "Mousedown": throw "impossible";
	 case "Mouseup": return {t: "hover", mp: ms.now};
	 case "Mouseleave": return {...ms, now: null};
	 default: throw unreachable(a);
	 }

  case "dragPat":
	 switch(a.t) {
	 case "Mousemove": return {...ms, now: a.mpoint};
	 case "Mousedown": throw "impossible";
	 case "Mouseup": return {t: "hover", mp: ms.now};
	 case "Mouseleave": return {...ms, now: null};
	 default: throw unreachable(a);
	 }
  default: throw unreachable(ms);
  }
}

function editPattern(state: Im<AppState>, mp: mpoint): Im<AppState> {
  const song: Im<PatUse[]> = getIn(state, x => x.score.song);
  const pu = find_pat_use(toJS(song), mp);
  if (pu != undefined) {
	 return set(state, 'mode', fromJS<RollMode>({t: "editPattern", patName: pu.patName,
																mouseState: {t: 'hover', mp: null}}));
  }
  return state;
}

function songReduceMouse(state: Im<AppState>, ms: SongMouseState, a: MouseAction): Im<AppState> {
  let s = state;
  if (a.t == "Mousedown") {
	 const last = get(state, 'lastMouseDown');
	 if (last != undefined && Date.now() - (last as any) < DOUBLE_CLICK_SPEED) {
		return editPattern(state, a.mpoint);
	 }
	 s = set(state, 'lastMouseDown', Date.now() as any);
  }

  switch(ms.t) {
  case "dragPat":
	 const newStart = ms.patUse.start + (ms.now.x - ms.orig.x) / PIXELS_PER_TICK;
	 return updateSong(s, sng => setIn(sng, x => x[ms.patIx].start, newStart));
  default: return s;
  }
}

export function songReduce(state: Im<AppState>, mode: SongMode, a: MouseAction): Im<AppState> {
  const nmst = songNewMouseState(state, mode.mouseState, a);
  const nst = set(state, 'mode', fromJS<SongMode>({...mode, mouseState: nmst}));
  return songReduceMouse(nst, mode.mouseState, a);
}
