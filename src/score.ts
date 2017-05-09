// got these from 'overboard'
// https://twitter.com/jcreed/status/851457146852184065
// beepbox export to json then
// jq -c '[.channels[0,1,2].patterns[1].notes[]|{pitch:.pitches[0], time: [.points[0].tick, .points[1].tick]}]'  /tmp/BeepBox-Song.json

import { Score } from './types';
export const score: Score = {
  next_id: 17,
  "duration": 65, // extra 1 to make it not click when I do a release
  "seconds_per_tick": 0.09,
  song: [{"lane": 1, "patName": "default", "start": 0, "duration": 32}],
  "patterns": {
	 "default":  {length: 32, notes: [
		{
		  id: 0,
		  pitch: 50,
		  time: [
			 0,
			 4
		  ]
		},
		{
		  id: 1,
		  pitch: 54,
		  time: [
			 4,
			 8
		  ]
		},
		{
		  id: 2,
		  pitch: 54,
		  time: [
			 8,
			 12
		  ]
		},
		{
		  id: 3,
		  pitch: 52,
		  time: [
			 12,
			 16
		  ]
		},
		{
		  id: 4,
		  pitch: 50,
		  time: [
			 16,
			 24
		  ]
		},
		{
		  id: 5,
		  pitch: 50,
		  time: [
			 28,
			 32
		  ]
		},
		{
		  id: 6,
		  pitch: 42,
		  time: [
			 0,
			 4
		  ]
		},
		{
		  id: 7,
		  pitch: 45,
		  time: [
			 4,
			 8
		  ]
		},
		{
		  id: 8,
		  pitch: 45,
		  time: [
			 8,
			 12
		  ]
		},
		{
		  id: 9,
		  pitch: 43,
		  time: [
			 12,
			 16
		  ]
		},
		{
		  id: 10,
		  pitch: 42,
		  time: [
			 16,
			 20
		  ]
		},
		{
		  id: 11,
		  pitch: 43,
		  time: [
			 20,
			 24
		  ]
		},
		{
		  id: 12,
		  pitch: 45,
		  time: [
			 24,
			 26
		  ]
		},
		{
		  id: 13,
		  pitch: 43,
		  time: [
			 26,
			 28
		  ]
		},
		{
		  id: 14,
		  pitch: 42,
		  time: [
			 28,
			 32
		  ]
		},
		{
		  id: 15,
		  pitch: 26,
		  time: [
			 0,
			 4
		  ]
		},
		{
		  id: 16,
		  pitch: 23,
		  time: [
			 16,
			 20
		  ]
		}
	 ]}
  }

};
