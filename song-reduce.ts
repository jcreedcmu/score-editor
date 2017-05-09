import { Song, MouseAction, Action, cpoint, PatUse } from './types';
import { AppState } from './state';
import { SongMode, SongMouseState } from './song-util';
import { RollMouseState, RollMode } from './roll-util';
import { PIXELS_PER_TICK, LANE_HEIGHT, TICKS_PER_GRID } from './song-editor';
import { Immutable as Im, get, getIn, set, update, setIn, fromJS, toJS } from './immutable';
import { getSong, updateSong, setCurrentPat, currentPatUndefined, modeEditPattern } from './accessors';
import { augment_and_snap } from './util';
import { unreachable } from './main';

const GRID_SNAP = TICKS_PER_GRID
const DOUBLE_CLICK_SPEED = 300;

function find_pat_use(song: Song, cp: cpoint): PatUse | undefined {
  const {x, y} = cp;
  return song.find(pu => x >= pu.start * PIXELS_PER_TICK && x <= (pu.start + pu.duration) * PIXELS_PER_TICK &&
						 y >= pu.lane * LANE_HEIGHT && y <= (pu.lane + 1) * LANE_HEIGHT);
}

function find_pat_use_index(song: Song, cp: cpoint): number {
  const {x, y} = cp;
  return song.findIndex(pu => x >= pu.start * PIXELS_PER_TICK && x <= (pu.start + pu.duration) * PIXELS_PER_TICK &&
								y >= pu.lane * LANE_HEIGHT && y <= (pu.lane + 1) * LANE_HEIGHT);
}

export function songNewMouseState(state: Im<AppState>, ms: SongMouseState, a: MouseAction): SongMouseState {
  const notes = getSong(state);
  switch(ms.t) {
  case "hover":
	 switch(a.t) {
	 case "Mousemove": return {t: "hover", mp: a.p};
	 case "Mousedown": return {t: "down", orig: a.p, now: a.p};
	 case "Mouseup": return ms; // this happens for mouse events that started outside the editor
	 case "Mouseleave": return {...ms, mp: null};
	 default: throw unreachable(a);
	 }

  case "down":
	 switch(a.t) {
	 case "Mousemove": {
		const pa: cpoint = ms.orig;
		const pb: cpoint = a.p;
		let rv: SongMouseState = {t: "down", orig: pa, now: pb};
		if (Math.abs(pa.x - pb.x) > 3 || Math.abs(pa.y - pb.y) > 3) {
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
	 case "Mousemove": return {...ms, now: a.p};
	 case "Mousedown": throw "impossible";
	 case "Mouseup": return {t: "hover", mp: ms.now};
	 case "Mouseleave": return {...ms, now: null};
	 default: throw unreachable(a);
	 }
  default: throw unreachable(ms);
  }
}

function editPattern(state: Im<AppState>, mp: cpoint): Im<AppState> {
  const song: Im<PatUse[]> = getIn(state, x => x.score.song);
  const pu = find_pat_use(toJS(song), mp);
  if (pu != undefined) {
	 return modeEditPattern(state, pu.patName);
  }
  return state;
}

function songReduceMouse(state: Im<AppState>, ms: SongMouseState, a: MouseAction): Im<AppState> {
  let s = state;
  if (a.t == "Mousedown") {
	 const last = get(state, 'lastMouseDown');
	 if (last != undefined && Date.now() - (last as any) < DOUBLE_CLICK_SPEED) {
		return editPattern(state, a.p);
	 }
	 s = set(state, 'lastMouseDown', Date.now() as any);
  }

  switch(ms.t) {
  case "dragPat":
	 if (a.t == "Mousemove") {
		const newStart = ms.patUse.start + GRID_SNAP * augment_and_snap((a.p.x - ms.orig.x) / PIXELS_PER_TICK / GRID_SNAP);
		const newLane = ms.patUse.lane + augment_and_snap((a.p.y - ms.orig.y) / LANE_HEIGHT);
		const s2 = updateSong(s, sng => setIn(sng, x => x[ms.patIx].start, newStart));
		return updateSong(s2, sng => setIn(sng, x => x[ms.patIx].lane, newLane));
	 }
  default: return s;
  }
}

export function songReduce(state: Im<AppState>, mode: SongMode, a: MouseAction): Im<AppState> {
  const nmst = songNewMouseState(state, mode.mouseState, a);
  const nst = set(state, 'mode', fromJS<SongMode>({...mode, mouseState: nmst}));
  return songReduceMouse(nst, mode.mouseState, a);
}
