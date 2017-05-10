import { Song, MouseAction, Action, cpoint, PatUse, LoopEndpoint } from './types';
import { AppState } from './state';
import { SongMode, SongMouseState } from './song-util';
import { RollMouseState, RollMode } from './roll-util';
import { PIXELS_PER_TICK, LANE_HEIGHT, TICKS_PER_GRID } from './song-editor';
import { Immutable as Im, get, getIn, set, update, setIn, fromJS, toJS } from './immutable';
import { getSong, updateSong, setCurrentPat, currentPatUndefined, modeEditPattern } from './accessors';
import { augment_and_snap, findLastOpt, FindInfo } from './util';
import { unreachable } from './main';

const GRID_SNAP = TICKS_PER_GRID
const DOUBLE_CLICK_SPEED = 300;
const PATUSE_RESIZE_MARGIN = 20;

type PatUseInfo = { pu: PatUse, rel: cpoint }

function find_pat_use(song: Song, cp: cpoint): FindInfo<PatUseInfo> | undefined {
  return findLastOpt(song, pu => {
	 const rel: cpoint = { x: cp.x - pu.start * PIXELS_PER_TICK, y: cp.y - pu.lane * LANE_HEIGHT };
	 if (rel.x >= 0 && rel.x <= pu.duration * PIXELS_PER_TICK &&
		  rel.y >= 0 && rel.y <= LANE_HEIGHT) {
		return { pu, rel };
	 }
  });
}


export function songNewMouseState(state: Im<AppState>, ms: SongMouseState, a: MouseAction): SongMouseState {
  const notes = getSong(state);
  switch(ms.t) {
  case "hover":
	 switch(a.t) {
	 case "Mousemove": return {t: "hover", mp: a.p};
	 case "Mousedown":
		if (a.extra != undefined) {
		  const which: LoopEndpoint = a.extra as LoopEndpoint;
		  return {t: "moveLoopEndpoint", orig: a.p, now: a.p, orig_val: getIn(state, s => s.score[which]), which};
		}
		return {t: "down", orig: a.p, now: a.p};
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
		  const pui = find_pat_use(notes, pa);
		  if (pui != undefined) {
			 const patIx = pui.index;
			 const song = getSong(state);
			 const patUse = pui.item.pu;
			 if (patUse.duration * PIXELS_PER_TICK - pui.item.rel.x < PATUSE_RESIZE_MARGIN) {
				rv = {t: "resizePat", orig: pa, now: pb, patUse, patIx};
			 }
			 else {
				rv = {t: "dragPat", orig: pa, now: pb, patUse, patIx};
			 }
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

  case "resizePat":
	 switch(a.t) {
	 case "Mousemove": return {...ms, now: a.p};
	 case "Mousedown": throw "impossible";
	 case "Mouseup": return {t: "hover", mp: ms.now};
	 case "Mouseleave": return {...ms, now: null};
	 default: throw unreachable(a);
	 }

  case "moveLoopEndpoint":
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
  const pu = find_pat_use(toJS(song), mp).item.pu;
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
	 else
		return state;
  case "resizePat":
	 if (a.t == "Mousemove") {
		const newDur = Math.max(GRID_SNAP, ms.patUse.duration + GRID_SNAP * augment_and_snap((a.p.x - ms.orig.x) / PIXELS_PER_TICK / GRID_SNAP));


		return updateSong(state, sng => setIn(sng, x => x[ms.patIx].duration, newDur));

	 }
	 else
		return state;
  case "moveLoopEndpoint":
	 if (a.t == "Mousemove") {
		const newVal = ms.orig_val + GRID_SNAP * augment_and_snap((a.p.x - ms.orig.x) / PIXELS_PER_TICK / GRID_SNAP);
		return setIn(state, s => s.score[ms.which], newVal);

	 }
  default: return s;
  }
}

export function songReduce(state: Im<AppState>, mode: SongMode, a: MouseAction): Im<AppState> {
  const nmst = songNewMouseState(state, mode.mouseState, a);
  const nst = set(state, 'mode', fromJS<SongMode>({...mode, mouseState: nmst}));
  return songReduceMouse(nst, mode.mouseState, a);
}
