export type Note = { pitch: number, time: [number, number] };

// the interface names should probably not be needed outside this
// module, only the tag names, which I'm by convention keeping the
// same as them.
interface PreviewNote {
  t: "PreviewNote";
  note: Note | null;
  exist?: boolean;
}
interface CreateNote {
  t: "CreateNote";
  note: Note;
}
interface DeleteNote {
  t: "DeleteNote";
  note: Note;
}
interface Play {
  t: "Play";
  score: Score;
}
interface SetCurrentPlaybackTime { t: "SetCurrentPlaybackTime", v: number }
export type Action =
  PreviewNote
  | CreateNote
  | DeleteNote
  | Play
  | SetCurrentPlaybackTime;

export type Score = {
  duration: number, // ticks
  seconds_per_tick: number,
  notes: Note[],
};

export type AppState = {
  offsetTicks: number | null,
  previewNote: Note | null,
  score: Score
};
