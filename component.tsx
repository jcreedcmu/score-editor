import { h as hh, render, Component } from 'preact';
import { RollEditor, RollEditorProps, rollDims } from './roll';
import { Minibuffer } from './minibuf';
import { dispatch, unreachable } from './main';
import { AppState, Mode } from './types';
import * as CSSTransitionGroup from 'preact-css-transition-group';

function ModeComponent({props}:{props: AppState}): JSX.Element {
  const mode: Mode = props.mode;
  switch (mode.t) {
	 case "editPattern":
		const { offsetTicks, mouseState, gridSize, scrollOctave, previewNote } = props;
		const rollProps: RollEditorProps = {
        ...rollDims,
		  offsetTicks, mouseState, gridSize, scrollOctave, previewNote,
		  notes: props.score.patterns[props.mode.patName],
		};
		return <RollEditor {...rollProps}/>;
	 case "fake":
		// typescript doesn't like reasoning about unary branch types??
		break;
	 default:
		throw unreachable(mode);
  }
}

export function component_render(props: AppState) {
  const cont = document.getElementById('canvas_container');
  const playClick = () => dispatch({t: "Play", score: props.score});

  const cc = <div>
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
  </div>;
  render(cc, cont, cont.lastElementChild);
}
