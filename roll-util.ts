export function y0pitch_of_scrollOctave(scrollOctave) {
  return 12 * (9 - scrollOctave) - 1;
}

export const SCALE = 2; // units: pixels per fat pixel
export const PIANO_H = 97;
export const PIANO_W = 58;
export const PIANO_OCTAVE_VSPACE = (PIANO_H - 1) * SCALE;
export const PIANO_WIDTH = (PIANO_W) * SCALE;
export const GUTTER_W = 8;
export const GUTTER_WIDTH = GUTTER_W * SCALE;
export const SCORE_W = 250;
export const SCORE_WIDTH = SCORE_W * SCALE;
export const FAT_PIXELS_PER_TICK = 6;
export const PIXELS_PER_TICK = FAT_PIXELS_PER_TICK * SCALE;
export const PITCH_HEIGHT = 8;
export const BLACK_NOTE_WIDTH = 34;

export const rollDims = {
  w: PIANO_WIDTH + GUTTER_WIDTH + SCORE_WIDTH,
  h: PIANO_OCTAVE_VSPACE * 3 + SCALE
};
