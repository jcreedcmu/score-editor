import { score } from './score';
import { component_render, find_note_at_mpoint } from './component';
import { MouseState, MouseAction, Action, AppState, Note, mpoint } from './types';
import * as _ from "underscore";

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
  document.onkeydown = (e) => {
	 switch(e.keyCode) {
	 case 188: dispatch({t: "IncrementGridSize", by: -1});
		break;
	 case 190: dispatch({t: "IncrementGridSize", by: 1});
		break;
	 default: console.log(e.keyCode);
	 }
  }
  component_render(state);
}

// Picked up this notion from
// http://stackoverflow.com/questions/39419170/how-do-i-check-that-a-switch-block-is-exhaustive-in-typescript
// not sure if there's a better way of doing it.
function unreachable(x: never): never {
  throw new Error("Shouldn't get here.");
}

let state: AppState = {
  offsetTicks: null,
  mouseState: {t: "absent"},
  previewNote: null,
  score,
  gridSize: 4,
  scrollOctave: 3, /* in the range [0 .. 4] for now */
};

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
		const found = find_note_at_mpoint(state.score.notes, mh);
		if (found) return found;
		return snap(state.gridSize, {pitch: mh.pitch,
											  time: [mh.time, mh.time]});
	 case "absent":
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
	 case "absent": return [true, {t: "hover", mp: a.mpoint}];
	 case "hover": return [false, {t: "hover", mp: a.mpoint}];
	 case "down": return [false, {t: "down", orig: ms.orig, now: a.mpoint}];
	 default: unreachable(ms);
	 }
  case "Mousedown":
	 switch(ms.t) {
	 case "absent": throw "impossible";
	 case "hover": return [true, {t: "down", orig: a.mpoint, now: a.mpoint}];
	 case "down": throw "impossible";
	 default: unreachable(ms);
	 }
  case "Mouseup":
	 switch(ms.t) {
	 case "absent": return [true, {t: "absent"}];
	 case "hover": throw "impossible";
	 case "down": return [true, {t: "hover", mp: a.mpoint}];
	 default: unreachable(ms);
	 }
  case "Mouseleave":
	 switch(ms.t) {
	 case "absent": throw "impossible";
	 case "hover": return [true, {t: "absent"}];
	 case "down": return [true, {t: "absent"}];
	 default: unreachable(ms);
	 }
  }
}

function note_of_mpoint({pitch, time}: mpoint): Note {
  return {pitch, time: [time, time + 3]};
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
		  state = rederivePreviewNote({...state, score: {...state.score,
																		 notes: _.filter(state.score.notes, notIt)}});
		}
		else {
		  // Create note
		  const sn: Note = snap(state.gridSize, note_of_mpoint(mp));
		  state = rederivePreviewNote({...state, score: {...state.score, notes: [...state.score.notes, sn]}});
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
  case "CreateNote":
	 const sn: Note = snap(state.gridSize, a.note);
	 // maybe I want immutable.js here!
	 state = rederivePreviewNote({...state, score: {...state.score, notes: [...state.score.notes, sn]}});
	 component_render(state);
	 break;
  case "DeleteNote":
	 const notIt = x => JSON.stringify(x) != JSON.stringify(a.note);
	 state = rederivePreviewNote({...state, score: {...state.score, notes: _.filter(state.score.notes, notIt)}});
	 component_render(state);
	 break;
  case "IncrementGridSize":
	 state = rederivePreviewNote({...state, gridSize: state.gridSize + a.by});
	 component_render(state);
	 break;
  case "Vscroll":
	 state = rederivePreviewNote({...state, scrollOctave: a.top});
	 component_render(state);
	 break;
  default: unreachable(a);
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
