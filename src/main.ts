import { score } from './score';
import { component_render } from './component';
import { Action, Note, PatUse } from './types';
import { AppState, Mode, initialState } from './state';
import { keyOf } from './key';
import { Immutable as Im, get, set, update, updateIn, fromJS, toJS } from './immutable';
import { play, stop } from './audio';
import { rollReduce, rollReduceConsistent } from './roll-reduce';
import { mpoint } from './roll-util';
import { songReduce } from './song-reduce';
import { setCurrentPat, currentPatUndefined, updateCurrentNotes, ensurePatternExists,
			updateCurrentPat } from './accessors';

declare const debug_glob: any;

const notes = score.patterns['default'].notes;

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
export function snap(gridSize: number, noteSize: number, mp: mpoint): Note {
  const gs = gridSize;
  const b = Math.floor(mp.time / gs) * gs;
  return {pitch: mp.pitch, time: [b, b + noteSize]};
}

function reduceCmd(state: Im<AppState>, cmd: string): Im<AppState> {
  const words = cmd.split(/ /);
  switch (words[0]) {
  case "create":
	 const patName = words[1];
	 const newPatUse: PatUse = { lane: 0, patName, start: 0, duration: 32 };
	 return ensurePatternExists(updateIn(state, x => x.score.song, x => fromJS( toJS(x).concat(newPatUse))), patName);
  case "clear":
	 return updateCurrentNotes(state, x => fromJS([]));
  case "length":
	 return updateCurrentPat(state, pat => set(pat, 'length', parseInt(words[1])));
  case "edit":
	 let st = set(state, 'mode', fromJS({t: 'editPattern', patName: words[1], mouseState: {t: "hover", mp: null }}));
	 if (currentPatUndefined(st)) {
		st = setCurrentPat(st, {notes: [], length: 32});
	 }
	 return st;
  default: return state;
  }
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
		return rollReduce(state, mode, a);
	 case "editSong":
		return songReduce(state, mode, a);
	 default: return state;
	 }
  case "Play":
	 play();
	 return state;
  case "Stop": {
	 stop();
 	 const ss = set(state, 'offsetTicks', undefined);
	 const s2 = set(ss, 'debugOffsetTicks', undefined);
	 return s2;
  }
  case "ContinuePlayback": {
	 const score = toJS(get(state, 'score'));
	 const progress = a.cb(score);
 	 const ss = set(state, 'offsetTicks', progress.v);
	 const s2 = set(ss, 'debugOffsetTicks', progress.dv);
	 return s2;
  }

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
	 return set(state, 'mode', fromJS<Mode>({t: "editSong", mouseState: {t: "hover", mp: null }}));

  default: unreachable(a);
  }
}

export function reduceConsistent(state: Im<AppState>, a: Action): Im<AppState> {
  const ns = reduce(state, a);
  const mode = toJS<Mode>(get(ns, 'mode'));
  switch(mode.t) {
  case "editPattern":
	 return rollReduceConsistent(ns, mode.mouseState);
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
  component_render(state);
}

// debugging
setTimeout(() => {
  window['score'] = score;
  for (let x in debug_glob) {
	 window[x] = debug_glob[x];
  }
}, 0);
