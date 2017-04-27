import { score } from './score';
import { component_render } from './component';
import { Action, AppState, Note, mpoint, Mode, initialState } from './types';
import { keyOf } from './key';
import { Immutable as Im, get, set, update, fromJS, toJS } from './immutable';
import { play } from './audio';
import { rollReduce, rollReduceConsistent } from './roll-reduce';
import { setCurrentPat, currentPatUndefined, updateCurrentNotes } from './accessors';

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
export function snap(gridSize: number, noteSize: number, mp: mpoint): Note {
  const gs = gridSize;
  const b = Math.floor(mp.time / gs) * gs;
  return {pitch: mp.pitch, time: [b, b + noteSize]};
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
  component_render(toJS(state));
}

// debugging
setTimeout(() => {
  window['score'] = score;
  for (let x in debug_glob) {
	 window[x] = debug_glob[x];
  }
}, 0);
