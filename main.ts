import { score } from './score';
import { component_render } from './component';
import { Action, AppState, Note } from './types';
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
  mouseHover: null,
  previewNote: null,
  score,
  gridSize: 4,
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
	 const mh = state.mouseHover;
	 if (mh == null)
		return null;
	 const found = _.find(state.score.notes, note => {
		return (note.pitch == mh.pitch
				  && note.time[0] <= mh.time
				  && note.time[1] >= mh.time);
	 });
	 if (found) return found;
	 return snap(state.gridSize, {pitch: mh.pitch,
											time: [mh.time, mh.time]});
  }
	 // if (a.note != null && !a.exist) {
	 // 	snap(a.note);
	 // }
  return {...state, previewNote: compute()};
}

// Any state -> state functions that effectfully happen here should
// commute with the evident projection from AppState to BaseState in the
// sense of
//                     effect
// Base x Derived ---------------> Base x Derived
//      |                               ^
//      |                               |
//  pi1 |                               | derive
//      |                               |
//      v                               |
//    Base -------------------------> Base
//          underlying state change

export function dispatch(a: Action) {
  switch (a.t) {
  case "SetHover":
	 const old = state;
	 state = rederivePreviewNote({...state, mouseHover: a.mpoint});
	 if (JSON.stringify(old.previewNote) != JSON.stringify(state.previewNote)) {
		component_render(state);
	 }
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
	 effState(s => ({...s, score: {...s.score, notes: [...s.score.notes, sn]}}));
	 break;
  case "DeleteNote":
	 const notIt = x => JSON.stringify(x) != JSON.stringify(a.note);
	 effState(s => ({...s, score: {...s.score, notes: _.filter(s.score.notes, notIt)}}));
	 break;
  case "IncrementGridSize":
	 state = rederivePreviewNote({...state, gridSize: state.gridSize + a.by});
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
