
type Note = { pitch: number, time: [number, number] };

// the interface names should probably not be needed outside this
// module, only the tag names, which I'm by convention keeping the
// same as them.
interface PreviewNote { t: "PreviewNote"; note: Note | null }
interface Play { t: "Play" }
interface SetCurrentPlaybackTime { t: "SetCurrentPlaybackTime", v: number }
export type Action = PreviewNote | Play | SetCurrentPlaybackTime;
