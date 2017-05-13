import { Score, IdNote, Progress } from './types';
import { dispatch } from './main';
import { Instrument } from './types'
import { getPatInst } from './pattern-util';

const COAST_MARGIN = 0.1; // seconds
const WARMUP_TIME = 0.05; // seconds
const UPDATE_INTERVAL = 0.025; // seconds
const RENDER_CHUNK_SIZE = 4096; // frames

export const ad = new AudioContext();
const RATE = ad.sampleRate; // most likely 44100, maybe 48000?
// units: audio frames per second

function freq_of_pitch(pitch) {
  return 440 * Math.pow(2, (pitch - 69) / 12);
}

const global_adsr_params = {a: 0.01, d: 0.1, s: 0.5, r: 0.01};

// a, d, r are all intended to be in seconds
// --- but the function would still work more or less the same for
// them being in any time unit, as long as they're all the same.
// s is a unitless scaling factor.
type adsrParams = {a: number, d: number, s: number, r: number};
function ads(params: adsrParams) {
  const {a, d, s} = params;
  return  (t => {
	 if (t < a)
		return t / a;
	 else if (t - a < d) {
		const T = (t - a) / d;
		return s * T + (1 - T);
	 }
	 else {
		return s;
	 }
  });
}

const NOISE_LENGTH = 44100;
const noise = [];
for (var i = 0; i < NOISE_LENGTH; i++) {
  noise[i] = Math.random() - 0.5;
}

type Liveness = "live" | "moribund" | "dead";

type NoteState = {
  liveness: Liveness,
  instrument: Instrument,
  envAge: number, // frames
  id: string,
  pitch: number,
  phase: number,
  freq: number,
  buf: number,
//  maturityTicks: number,
}

type ChunkTiming = {
  startFrame: number, // frames relative to render chunk start
  endFrame?: number, // frames relative to render chunk start
//  maturityTicks: number, // how old the note already in the score at time of render chunk start
}

type ClipState = { state: NoteState } & ChunkTiming


type ClipNote = IdNote & ChunkTiming & { instrument: Instrument }


// Leave behind some breadcrumbs about contiguous chunks we've
// rendered, so we can properly communicate upstream where in the song
// we're currently playing.
type NowTicksChunk = {
  startSecs: number,
  startTicks: number,
  durationSecs: number,
  secsPerTick: number
}

type AudioState = {
  // the timeout id of the setTimeout for our next update, in case we
  // want to cancel it
  nextUpdateTimeout? : number,

  // The point in time that we've 'rendered until'. That is, the first
  // moment for which we haven't already computed audio frames and
  // sent off to the audioctx to be played at a certain time. This will always
  // be a little bit into the future. Whenever it gets too close to the present
  // (i.e. less than COAST_MARGIN) we'll render some more.
  renderedUntil?: number, // seconds since audiocontext initialization
  renderedUntilSong? : number, // ticks since beginning of song

  liveNotes: NoteState[],
  nowTicks: NowTicksChunk[],
}

const state : AudioState = {
  liveNotes: [],
  nowTicks: [],
};

function repeats(patUseLength: number, patLength: number): {offset: number, duration: number}[] {
  let remaining: number = patUseLength;
  let pos = 0;
  let rv: {offset: number, duration: number}[] = [];
  while (remaining > patLength) {
	 rv.push({offset: pos, duration: patLength});
	 remaining -= patLength;
	 pos += patLength;
  }
  rv.push({offset: pos, duration: remaining});
  return rv;
}

// start and duration are in ticks
function collectNotes(score: Score, start: number, duration: number): ClipNote[] {
  const rv: ClipNote[] = [];

  const ct = [start, start + duration]; // am I fenceposting wrong?
  for (const pu of score.song) {
	 const pu_offset = pu.start;
	 const pat = score.patterns[pu.patName];

	 repeats(pu.duration, pat.length).forEach(({offset, duration}) => {
		pat.notes.forEach(note => {
		  const off = offset + pu_offset;
		  const noteStart = note.time[0];
		  if (noteStart >= duration) return;
		  const end = Math.min(note.time[1], duration);
		  const nt: [number, number] = [off + noteStart, off + end];
		  if (nt[0] <= ct[1] && ct[0] <= nt[1]) {
			 const cn: ClipNote = {
				  ...note,
				id: note.id + "__" + pu.lane,
				time: nt,
				instrument: getPatInst(pu.patName, pat),
				startFrame: Math.round((Math.max(nt[0], ct[0]) - ct[0]) * (score.seconds_per_tick * RATE)),
				endFrame: Math.round((Math.min(nt[1], ct[1]) - ct[0]) * (score.seconds_per_tick * RATE)),
//				maturityTicks: ct[0] - nt[0],
			 };
			 rv.push(cn);
		  }
		});
	 });
  }
  return rv;
}


// XXX: mutates oldNotes. Harmless for now, since I think every caller
// essentially treates it linearly, but still I think it would be
// nicer to be purely functional.
function mergeNotes(oldNotes: NoteState[], newNotes: ClipNote[]): ClipState[] {
  const newMerged: ClipState[] = [];
  newNotes.forEach(note => {
	 const matchingNoteIx = oldNotes.findIndex(n => n.id == note.id); // check for more matching data? maturityTicks?
	 let state: NoteState;
	 if (note.startFrame == 0 && matchingNoteIx != -1) {
	 	state = oldNotes.splice(matchingNoteIx, 1)[0];
	 }
	 else {
	 	state = {
	 	  instrument: note.instrument,
		  liveness: "live",
	 	  id: note.id,
	 	  phase: 0,
		  envAge: 0,
	 	  pitch: note.pitch,
//		  maturityTicks: note.maturityTicks,
	 	  freq: freq_of_pitch(note.pitch), // TODO: having both pitch and freq here is kinda redundant, eliminate one
	 	  buf: 0,
	 	};
	 }
	 newMerged.push({state,
						  startFrame: note.startFrame,
						  endFrame: note.endFrame,
//						  maturityTicks: note.maturityTicks
						 });
  });
  const moribund: ClipState[] = oldNotes.map(note => ({
	 state: {...note, liveness: "moribund" as Liveness},
	 startFrame: 0,
//	 maturityTicks: note.maturityTicks,
  }));
  return newMerged.concat(moribund);
}

function newLiveNotes(mergedNotes: ClipState[]): NoteState[] {
  return mergedNotes.map(x => x.state);
}

// Same as renderChunkInto below, except
// (a) only fill the part of dat starting at datStart and proceeding for datDuration frames
// (b) we're guaranteed the interval [startTicks, startTicks + datDuration * frames_per_tick]
//     is logically contiguous; i.e. doesn't wrap across a loop point.

function renderContiguousChunkInto(
  dat: Float32Array,
  datStart: number, // frames
  datDuration: number, // frames
  startTicks: number, // ticks
  score: Score,
  liveNotes: NoteState[]
): NoteState[] {
  const collectedNotes = collectNotes(score, startTicks, datDuration / (score.seconds_per_tick * RATE));
  const mergedNotes = mergeNotes(liveNotes, collectedNotes);
  for (const cs of mergedNotes) {
	 const noteState = cs.state;
	 const startFrame = cs.startFrame;
	 const endFrame = cs.endFrame;

	 const adsr_params = {...global_adsr_params};
	 if (noteState.instrument == "drums") {
		adsr_params.r = 0.2;
		adsr_params.a = 0.001;
		adsr_params.d = 0.0;
		adsr_params.s = 1.000;
	 }
	 const env_f = ads(adsr_params);

	 switch (noteState.instrument) {
	 case "sine":
		for (let i = startFrame; i < datDuration; i++) {
		  const env = noteState.liveness == "live" ?
			 env_f(noteState.envAge / RATE)
			 : 1 - noteState.envAge / adsr_params.r;
		  dat[datStart + i] += env * 0.15 * ((noteState.phase - Math.floor(noteState.phase)) < 0.5 ? 0.2 : -0.2);
		  noteState.phase += noteState.freq / RATE;
		  noteState.envAge++;
		  if (noteState.liveness == "live") {
			 if (i >= endFrame) {
				noteState.liveness = "moribund";
				noteState.envAge = 0;
			 }
		  }
		  else if (noteState.liveness == "moribund" && noteState.envAge >= adsr_params.r) {
			 noteState.liveness = "dead";
			 break;
		  }
		}
		break;
	 case "drums":
		// const step = Math.pow(2, (noteState.pitch - 60) / 1.5);
		// const p = Math.min(1.0, noteState.freq * 8.0 / RATE);
		// const volumeAdjust = Math.pow(2.0, (50-noteState.pitch) / 12);
		// for (let i = note_start_frame; i < datStart + datDuration; i++) {
		//   const env = env_f((i - note_start_frame) / RATE + noteState.envAge);
		//   noteState.phase += step;
		//   if (noteState.phase >= NOISE_LENGTH) { noteState.phase -= NOISE_LENGTH; }
		//   noteState.buf = (1-p) * noteState.buf + p * noise[Math.floor(noteState.phase)];
		//   dat[datStart + i] += env * volumeAdjust * noteState.buf;
		// }
		break;
	 }
  }
  return newLiveNotes(mergedNotes);
}

type RenderChunkResult = {
  liveNotes: NoteState[],
  renderedUntilSong: number,
  nowTicks: NowTicksChunk[],
}

// Starting at song-time `startTicks`, given score `score`, assuming `liveNotes` notes exist from
// the previous chunk render, fill the audio buffer `dat` with samples, returning
// {liveNotes: the set of notes that are still active,
//  nowTicks: a list of mappings from real time to song time, relative to the beginning of this rendering,
//            i.e. startSecs of the first item will always be 0 and we trust the caller to bump it up to
//            the current time}
function renderChunkInto(dat: Float32Array, startTicks: number, score: Score, liveNotesIn: NoteState[]): RenderChunkResult {
  if (score.loop_end <= score.loop_start) { throw "invariant violation, loop markers can't be badly ordered" }

  const ticks_to_render = dat.length / (score.seconds_per_tick * RATE);
  if (startTicks < score.loop_start) startTicks = score.loop_start;
  if (startTicks + ticks_to_render <= score.loop_end) {
	 const liveNotes = renderContiguousChunkInto(dat, 0, dat.length, startTicks, score, liveNotesIn);
	 const nowTicks: NowTicksChunk[] = [
		{
		  startSecs: 0,
		  startTicks,
		  durationSecs: dat.length / RATE,
		  secsPerTick: score.seconds_per_tick
		}
	 ];
	 const renderedUntilSong = startTicks + ticks_to_render;
	 return {liveNotes, nowTicks, renderedUntilSong};
  }
  else {
	 const fragLength = Math.round((score.loop_end - startTicks) * (score.seconds_per_tick * RATE)); // frames
	 const liveNotes0 = renderContiguousChunkInto(dat, 0, fragLength, startTicks, score, liveNotesIn);
	 const liveNotes = renderContiguousChunkInto(dat, fragLength, dat.length - fragLength, score.loop_start, score, liveNotes0);
	 const renderedUntilSong = score.loop_start + ticks_to_render - fragLength / (score.seconds_per_tick * RATE);
	 const nowTicks: NowTicksChunk[] = [
		{
		  startSecs: 0,
		  startTicks,
		  durationSecs: fragLength / RATE,
		  secsPerTick: score.seconds_per_tick
		},
		{
		  startSecs: fragLength / RATE,
		  startTicks: score.loop_start,
		  durationSecs: (dat.length - fragLength) / RATE,
		  secsPerTick: score.seconds_per_tick
		}
	 ];
	 return {liveNotes, nowTicks, renderedUntilSong};
  }
}

// t is in seconds, return value is in ticks
function nowTicks(chunks: NowTicksChunk[], t: number): number {
  for (let i = 0; i < chunks.length; i++) {
	 const ch = chunks[i];
	 if (t >= ch.startSecs && t < ch.startSecs + ch.durationSecs) {
		return ch.startTicks + (t - ch.startSecs) / ch.secsPerTick;
	 }
  }
  throw `trying to determine song position of unrendered audio: ${t} not in ${JSON.stringify(chunks)}`;
}

function continuePlayback(score: Score): Progress {
  const now = ad.currentTime;

  // do we need to render?
  if ((state.renderedUntil - now) < COAST_MARGIN) {
	 const render_chunk_size_seconds = RENDER_CHUNK_SIZE / RATE;
	 const buf = ad.createBuffer(1 /* channel */, RENDER_CHUNK_SIZE, RATE);
	 const dat: Float32Array = buf.getChannelData(0);
	 const {liveNotes, renderedUntilSong, nowTicks} = renderChunkInto(dat, state.renderedUntilSong, score, state.liveNotes);
	 state.liveNotes = liveNotes;
	 state.renderedUntilSong = renderedUntilSong;

	 // As noted above, renderChunkInto gives us startSecs relative to
	 // the beginning of the renderedChunk. Adjust it to relative to
	 // audio context initialization time.
	 const nowTicksAbsolute = nowTicks.map(nt => ({...nt, startSecs: nt.startSecs + now}));

	 state.nowTicks = state.nowTicks.filter(nt => nt.startSecs + nt.durationSecs >= now).concat(nowTicksAbsolute);

	 const src = ad.createBufferSource();
	 src.buffer = buf;
	 src.connect(ad.destination);

	 // I expect
	 //
	 //     state.renderedUntil * RATE
	 //
	 // to stay very close to an integer (because audio context's
	 // "currentTime" seems to stay essentially an integer multiple of
	 // 1/RATE) although since I'm incrementing by floating point
	 // quantities of seconds, I observe it drifting by something on
	 // the order of 1e-8 seconds per second. Maybe could keep track of
	 // renderedUntilFrames as an integer instead. (no chance it'll get
	 // anywhere close to Number.MAX_SAFE_INTEGER in practice, I think)
	 src.start(state.renderedUntil);
	 state.renderedUntil += render_chunk_size_seconds;
  }

  state.nextUpdateTimeout = setTimeout(audioUpdate, UPDATE_INTERVAL * 1000);
  return {v: nowTicks(state.nowTicks, now)};
}

export function play() {
  if (state.nextUpdateTimeout) {
	 clearTimeout(state.nextUpdateTimeout);
  }

  state.liveNotes = [];
  state.renderedUntilSong = 0;
  state.renderedUntil = ad.currentTime + WARMUP_TIME;
  state.nextUpdateTimeout = setTimeout(audioUpdate, 0);
}

export function stop() {
  if (state.nextUpdateTimeout != undefined) {
	 clearTimeout(state.nextUpdateTimeout);
	 state.nextUpdateTimeout = undefined;
  }
}
function audioUpdate() {
  dispatch({t: "ContinuePlayback", cb: continuePlayback});
}
