export type Note = { pitch: number, time: [number, number] };

export type MouseAction =
  | { t: "Mousemove"; p: cpoint; }
  | { t: "Mousedown"; p: cpoint; }
  | { t: "Mouseup" }
  | { t: "Mouseleave" }

export type Action =
  MouseAction
  | { t: "Play"; score: Score; }
  | { t: "Vscroll"; top: number; }
  | { t: "SetCurrentPlaybackTime"; v: number, dv: number }
  | { t: "Key", key: string }
  | { t: "ExecMinibuf", cmd: string }
  | { t: "SetMinibuf", v: string }
  | { t: "EditSong" }
  | { t: "EditPat", patName: string }

export type Pattern = {
  length: number,
  notes: Note[],
};

export type PatUse = {
  patName: string,
  start: number,
  duration: number,
}

export type Song = PatUse[]

export type Score = {
  duration: number, // ticks
  seconds_per_tick: number,
  song: Song,
  patterns: {[P in string]: Pattern},
};

export type cpoint = { x: number, y: number } // point measured in pixels from the topleft of the canvas
