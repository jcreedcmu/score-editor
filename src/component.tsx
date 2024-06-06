import { h as hh, render, JSX } from 'preact';
import { RollEditor, RollEditorProps } from './roll';
import { rollDims } from './roll-util';
import { SongEditor } from './song-editor';
import { Minibuffer } from './minibuf';
import { dispatch, unreachable } from './main';
import { AppState, Mode } from './state';
import CSSTransitionGroup from 'preact-css-transition-group';
import { Immutable as Im, get, set, update, updateIn, fromJS, toJS } from './immutable';
import { getPatInst } from './pattern-util';

function ModeHeader({ mode }: { mode: Mode }): JSX.Element {
  switch (mode.t) {
    case "editPattern":
      return <div className="modeHeader">Pattern: {mode.patName}</div>;
    default:
      return <div className="modeHeader">Song</div>;
  }
}

function ModeComponent(mode: Mode, state: Im<AppState>): JSX.Element {
  switch (mode.t) {
    case "editPattern":
      const props: AppState = toJS(state);
      const { offsetTicks, debugOffsetTicks, gridSize, noteSize, scrollOctave, previewNote } = props;
      const pattern = props.score.patterns[mode.patName];
      const rollProps: RollEditorProps = {
        ...rollDims,
        offsetTicks, debugOffsetTicks, gridSize, noteSize, scrollOctave, previewNote,
        mouseState: mode.mouseState,
        useOffsetTicks: mode.useOffsetTicks,
        style: getPatInst(mode.patName, pattern) == 'drums' ? 'drums' : 'piano',
        pattern,
      };
      return <RollEditor {...rollProps} />;
    case "editSong":
      return <SongEditor state={state} />;
    default:
      throw unreachable(mode);
  }
}

export function component_render(props: Im<AppState>) {
  const cont = document.getElementById('canvas_container');
  const playClick = () => dispatch({ t: "Play" });
  const stopClick = () => dispatch({ t: "Stop" });
  const minibufferVisible = get(props, 'minibufferVisible');
  const minibuf = get(props, 'minibuf');
  const mode = toJS<Mode>(get(props, 'mode'));
  const cc =
    <div>
      <ModeHeader mode={mode} />
      <div className="workspace">
        {ModeComponent(mode, props)}
        <div class="controls">
          <button onClick={playClick}>Play</button><br /><br />
          <button onClick={stopClick}>Stop</button><br /><br />
        </div>
        <div>
          <div className="minibuffer">
            <CSSTransitionGroup transitionName="minibuf">
              {minibufferVisible ?
                <Minibuffer key="minibuf"
                  value={minibuf}
                  send={cmd => dispatch({ t: "ExecMinibuf", cmd })} /> : ''}
            </CSSTransitionGroup>
          </div>
        </div>
      </div>
    </div>;
  render(cc, cont, cont.lastElementChild);
}
