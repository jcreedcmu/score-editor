// got these from 'overboard'
// https://twitter.com/jcreed/status/851457146852184065
// beepbox export to json then
// jq -c '[.channels[0,1,2].patterns[1].notes[]|{pitch:.pitches[0], time: [.points[0].tick, .points[1].tick]}]'  /tmp/BeepBox-Song.json

import { Score } from './types';
export const score: Score = {
  "duration": 33, // extra 1 to make it not click when I do a release
  "seconds_per_tick": 0.09,
  "patterns": {
	 "default":  [
      {
		  "pitch": 50,
		  "time": [
			 0,
			 4
		  ]
      },
      {
		  "pitch": 54,
		  "time": [
			 4,
			 8
		  ]
      },
      {
		  "pitch": 54,
		  "time": [
			 8,
			 12
		  ]
      },
      {
		  "pitch": 52,
		  "time": [
			 12,
			 16
		  ]
      },
      {
		  "pitch": 50,
		  "time": [
			 16,
			 24
		  ]
      },
      {
		  "pitch": 50,
		  "time": [
			 28,
			 32
		  ]
      },
      {
		  "pitch": 42,
		  "time": [
			 0,
			 4
		  ]
      },
      {
		  "pitch": 45,
		  "time": [
			 4,
			 8
		  ]
      },
      {
		  "pitch": 45,
		  "time": [
			 8,
			 12
		  ]
      },
      {
		  "pitch": 43,
		  "time": [
			 12,
			 16
		  ]
      },
      {
		  "pitch": 42,
		  "time": [
			 16,
			 20
		  ]
      },
      {
		  "pitch": 43,
		  "time": [
			 20,
			 24
		  ]
      },
      {
		  "pitch": 45,
		  "time": [
			 24,
			 26
		  ]
      },
      {
		  "pitch": 43,
		  "time": [
			 26,
			 28
		  ]
      },
      {
		  "pitch": 42,
		  "time": [
			 28,
			 32
		  ]
      },
      {
		  "pitch": 26,
		  "time": [
			 0,
			 4
		  ]
      },
      {
		  "pitch": 23,
		  "time": [
			 16,
			 20
		  ]
      }
	 ]
  }

};
