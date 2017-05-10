export type Note = { pitch: number, time: [number, number] };
export type IdNote = Note & { id: string };
export type MouseAction =
  | { t: "Mousemove"; p: cpoint; }
  | { t: "Mousedown"; p: cpoint; }
  | { t: "Mouseup" }
  | { t: "Mouseleave" }

export type Progress = {v: number, dv: number}
export type ContinuePlaybackFunc = (score: Score) => Progress;
export type Action =
  MouseAction
  | { t: "Play" }
  | { t: "Stop" }
  | { t: "ContinuePlayback"; cb: ContinuePlaybackFunc }
  | { t: "Vscroll"; top: number; }
  | { t: "Key", key: string }
  | { t: "ExecMinibuf", cmd: string }
  | { t: "SetMinibuf", v: string }
  | { t: "EditSong" }

export type Pattern = {
  length: number,
  notes: IdNote[],
};

export type PatUse = {
  lane: number,
  patName: string,
  start: number,
  duration: number,
}

export type Song = PatUse[]

export type Score = {
  next_id: number,
  duration: number, // ticks
  seconds_per_tick: number,
  song: Song,
  patterns: {[P in string]: Pattern},
};

export type cpoint = { x: number, y: number } // point measured in pixels from the topleft of the canvas
