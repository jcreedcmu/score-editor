import { h as hh, render, Component } from 'preact';

// declare global { // https://github.com/Microsoft/TypeScript/issues/10628
//   interface CanvasRenderingContext2D {
// 	 imageSmoothingEnabled: boolean;
//   }
// }

export class Surface< P > extends Component< P, void > {
  ctx: CanvasRenderingContext2D;
  elt: HTMLCanvasElement;
  onmousedown(n:MouseEvent): void { }
  onmousemove(n:MouseEvent): void { }
  onmouseleave(n:MouseEvent): void { }
  className: string = null;
  key: string = null;
  w: number = 0;
  h: number = 0;

  extraAttrs(props: P) { return {}; }

  render (props: P, state: void): JSX.Element {
	 const rf = (elt: HTMLCanvasElement) => {
		if (!elt) {
		  // This happens when the elemaent being deleted, I
		  // gather this is my chance to clean up any side effects that
		  // the ref created if I wanted to
		  return;
		}
		this.elt = elt;
		this.ctx = elt.getContext('2d');
	 }
	 const attrs = {
		ref: rf,
		onmousedown: (ev:MouseEvent) => this.onmousedown(ev),
		onmousemove: (ev:MouseEvent) => this.onmousemove(ev),
		onmouseleave: (ev:MouseEvent) => this.onmouseleave(ev),
		className: this.className,
		key: this.key,
	 };
	 const e = this.extraAttrs(props);
	 for (const k in e) {
		attrs[k] = e[k];
	 }
	 return hh("canvas", attrs);
  }

  init() { }

  clear() {
	 this.ctx.clearRect(0, 0, this.w, this.h);
  }

  setDims(w: number, h: number) {
	 const oldWidth = w;
	 const oldHeight = h;
	 const ratio = devicePixelRatio;

	 this.w = this.elt.width = oldWidth;
	 this.h = this.elt.height = oldHeight;

	 this.elt.width = oldWidth * ratio;
	 this.elt.height = oldHeight * ratio;

	 this.elt.style.width = oldWidth + 'px';
	 this.elt.style.height = oldHeight + 'px';

	 this.ctx.imageSmoothingEnabled = false;
	 this.ctx.webkitImageSmoothingEnabled = false;
  }

  paint(props: P) {  }

  componentDidMount() {
	 this.init();
	 this.paint(this.props);
  }

  componentDidUpdate() {
	 this.paint(this.props);
  }
}
