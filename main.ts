import { score } from './score';
import { component_render, find_note_at_mpoint } from './component';
import { MouseState, MouseAction, Action, AppState, Note, mpoint,
			initialState } from './types';
import { keyOf } from './key';
import { updateIn } from './util';

import * as _ from "lodash";

export const ad = new AudioContext();
const RATE = ad.sampleRate; // most likely 44100, maybe 48000?

declare const debug_glob: any;

const notes = score.notes;
notes.forEach(note => note.pitch += 12);

function freq_of_pitch(pitch) {
  return 440 * Math.pow(2, (pitch - 69) / 12);
}

const global_adsr_params = {a: 0.01, d: 0.1, s: 0.5, r: 0.01};

function adsr(params, length) {
  const {a, d, s, r} = params;
  return {
	 env_f: (t => {
		if (t < a) { return t / a }
		if (t - a < d) { const T = (t - a) / d; return s * T + (1 - T); }
		if (t < length) return s;
		return s * (1 - (t - length) / r);
	 }),
	 real_length: length + r
  }
}


function audio_render_notes(ad, score) {
  const segmentTime = score.duration * score.seconds_per_tick;
  const len = segmentTime * RATE; // in frames
  var buf = ad.createBuffer(1, len, RATE);
  var dat = buf.getChannelData(0);

  score.notes.forEach(note => {
	 const {env_f, real_length} = adsr(global_adsr_params,
												  (note.time[1] - note.time[0]) * score.seconds_per_tick);
	 const note_start_frame = Math.round(note.time[0] * score.seconds_per_tick * RATE);
	 const note_term_frame = Math.round(note.time[0] * score.seconds_per_tick * RATE + real_length * RATE);
	 const state = {phase: 0, amp: 1, f: freq_of_pitch(note.pitch)};

	 for (var t = note_start_frame; t < note_term_frame; t++) {
		state.phase += state.f / RATE;
		let e = env_f((t - note_start_frame) / RATE);
		const wav = 0.15 * Math.sin(3.1415926535 * 2 * state.phase);
//		const wav = 0.05 * ((state.phase - Math.floor(state.phase) < 0.5) ? 1 : -1);
		dat[t] += e * state.amp * wav ;
	 }
  });

  var src = ad.createBufferSource();

  const beginTime = ad.currentTime + 0.1;

  const ival = setInterval(() => {
	 if (ad.currentTime < beginTime)
		return;
	 dispatch({t: "SetCurrentPlaybackTime",
				  v: (ad.currentTime - beginTime) / score.seconds_per_tick});
  }, 40);

  src.onended = () => {
	 dispatch({t: "SetCurrentPlaybackTime", v: null});
	 clearInterval(ival);
  }
  src.buffer = buf;
  src.connect(ad.destination);
  src.start(beginTime);
}

function play(score) {
  audio_render_notes(ad, score);
}

window.onload = () => {
  document.onkeydown = (e) => dispatch({t: "Key", key: keyOf(e)});
  document.onmouseup = (e) => dispatch({t: "Mouseup"});
  component_render(state);
}

// Picked up this notion from
// http://stackoverflow.com/questions/39419170/how-do-i-check-that-a-switch-block-is-exhaustive-in-typescript
// not sure if there's a better way of doing it.
function unreachable(x: never): never {
  throw new Error("Shouldn't get here.");
}

let state = initialState;
state.score = score;

// snap to grid
function snap(gridSize: number, note: Note): Note {
  const gs = gridSize;
  const b = Math.floor(note.time[0] / gs) * gs;
  return {pitch: note.pitch,
			 time: [b, b + gs]};
}

function rederivePreviewNote(state: AppState): AppState {
  function compute(): Note | null {
	 const ms = state.mouseState;
	 switch (ms.t) {
	 case "hover":
		const mh = ms.mp;
		if (mh == null)
		  return null;
		const found = find_note_at_mpoint(state.score.notes, mh);
		if (found) return found;
		return snap(state.gridSize, {pitch: mh.pitch,
											  time: [mh.time, mh.time]});
	 case "down":
		return null;
	 default: unreachable(ms);
	 }
  }
  return {...state, previewNote: compute()};

}

function mouseReduce(a: MouseAction, ms: MouseState): [boolean, MouseState] {
  switch(a.t) {
  case "Mousemove":
	 switch(ms.t) {
	 case "hover": return [false, {t: "hover", mp: a.mpoint}];
	 case "down": return [false, {t: "down", orig: ms.orig, now: a.mpoint}];
	 default: unreachable(ms);
	 }
  case "Mousedown":
	 switch(ms.t) {
	 case "hover": return [true, {t: "down", orig: a.mpoint, now: a.mpoint}];
	 case "down": throw "impossible";
	 default: unreachable(ms);
	 }
  case "Mouseup":
	 switch(ms.t) {
	 case "hover": return [false, ms]; // this happens for mouse events that started outside the editor
	 case "down": return [true, {t: "hover", mp: ms.now}];
	 default: unreachable(ms);
	 }
  case "Mouseleave":
	 switch(ms.t) {
	 case "hover": return [true, {...ms, mp: null}];
	 case "down": return [true, {...ms, now: null}];
	 default: unreachable(ms);
	 }
  }
}

function note_of_mpoint({pitch, time}: mpoint): Note {
  return {pitch, time: [time, time + 3]};
}

function reduceCmd(state: AppState, cmd: string): AppState {
  switch (cmd) {
  case "clear":
	 return {...state, score: {...state.score, notes: []}};
  default: return state;
  }
}
// For any f that dispatch causes as a side effect,
// there should exist an f' that makes the following
// diagram commute:
//                        f
//    Base x Derived ---------------> Base x Derived
//         ^                               ^
//  <id,   |                               |<id,
//  derive>|                               | derive>
//         |                               |
//         |                               |
//       Base -------------------------> Base
//                      f'
export function dispatch(a: Action) {
  switch (a.t) {
  case "Mousemove":
  case "Mouseleave":
  case "Mousedown":
  case "Mouseup":
	 const old = state;
	 const [redraw, nms] = mouseReduce(a, state.mouseState);
	 let red = redraw;
	 if (state.mouseState.t == "down" && a.t == "Mouseup") {
		const mp = state.mouseState.orig;
		const note = find_note_at_mpoint(state.score.notes, mp);
		if (note) {
		  // Delete note
		  const notIt = x => JSON.stringify(x) != JSON.stringify(note);
		  state = rederivePreviewNote(updateIn<AppState['score']['notes']>(state, ['score', 'notes'], n => _.filter(n, notIt)));
		}
		else {
		  // Create note
		  const sn: Note = snap(state.gridSize, note_of_mpoint(mp));
		  state = rederivePreviewNote(updateIn<AppState['score']['notes']>(state, ['score', 'notes'], n => n.concat([sn])));
		}
		red = true;
	 }
	 state = rederivePreviewNote({...state, mouseState: nms});
	 if (red || (JSON.stringify(old.previewNote) != JSON.stringify(state.previewNote)))
		component_render(state);
	 break;
  case "Play":
	 play(a.score);
	 break;
  case "SetCurrentPlaybackTime":
	 setState({offsetTicks: a.v});
	 break;
  case "Key": {
	 const old = state;
	 state = reduceKey(state, a.key);
	 if (state != old)
		component_render(state);
	 break;
  }
  case "Vscroll":
	 state = rederivePreviewNote({...state, scrollOctave: a.top});
	 component_render(state);
	 break;
  case "ExecMinibuf":
	 state = reduceCmd(state, state.minibuf);
	 state = {...state, minibufferVisible: false, minibuf: ''};
	 component_render(state);
	 break;
  case "SetMinibuf":
	 state = {...state, minibuf: a.v};
	 component_render(state);
	 break;
  default: unreachable(a);
  }
}

function reduceKey(state: AppState, key: string): AppState {
  switch(key) {
  case "A-x":
	 return {...state, minibufferVisible: !state.minibufferVisible};
  case ",":
	 if (state.minibufferVisible) return state;
	 return rederivePreviewNote({...state, gridSize: state.gridSize / 2});
  case ".":
	 if (state.minibufferVisible) return state;
	 return rederivePreviewNote({...state, gridSize: state.gridSize * 2});
  default: return state;
  }
}

function setState(extra) {
  state = {...state, ...extra};
  component_render(state);
}

function effState(f : (a: AppState) => AppState) {
  state = f(state);
  component_render(state);
}

// debugging
setTimeout(() => {
  window['score'] = score;
  for (let x in debug_glob) {
	 window[x] = debug_glob[x];
  }
}, 0);
