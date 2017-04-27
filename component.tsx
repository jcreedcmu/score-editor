import { h as hh, render } from 'preact';
import { RollEditor, RollEditorProps, rollDims } from './roll';
import { SongEditor } from './song_editor';
import { Minibuffer } from './minibuf';
import { dispatch, unreachable } from './main';
import { AppState, Mode } from './types';
import * as CSSTransitionGroup from 'preact-css-transition-group';

function ModeHeader({mode}:{mode: Mode}): JSX.Element {
  switch (mode.t) {
	 case "editPattern":
		return <div className="modeHeader">Pattern: {mode.patName}</div>;
	 default:
		return <div className="modeHeader">Song</div>;
  }
}

function ModeComponent({props}:{props: AppState}): JSX.Element {
  const mode: Mode = props.mode;
  switch (mode.t) {
	 case "editPattern":
		const { offsetTicks, gridSize, noteSize, scrollOctave, previewNote } = props;
		const rollProps: RollEditorProps = {
        ...rollDims,
		  offsetTicks, gridSize, noteSize, scrollOctave, previewNote,
		  mouseState: mode.mouseState,
		  style: mode.patName == "drums" ? "drums" : "piano",
		  pattern: props.score.patterns[mode.patName],
		};
		return <RollEditor {...rollProps}/>;
	 case "editSong":
		return <SongEditor {...props}/>;
	 default:
		throw unreachable(mode);
  }
}

export function component_render(props: AppState) {
  const cont = document.getElementById('canvas_container');
  const playClick = () => dispatch({t: "Play", score: props.score});

  const cc =
  <div>
	 <ModeHeader mode={props.mode} />
	 <div className="workspace">
		<button onClick={playClick}>Play</button><br/>
		<ModeComponent props={props} />
		<div>
		  <div className="minibuffer">
			 <CSSTransitionGroup transitionName="minibuf">
				{props.minibufferVisible ? <Minibuffer key="minibuf"
																	value={props.minibuf}
																	send={cmd => dispatch({t:"ExecMinibuf", cmd})} /> : ''}
			 </CSSTransitionGroup>
		  </div>
		</div>
	 </div>
  </div>;
  render(cc, cont, cont.lastElementChild);
}
