package sound;

import  log.Logger;

import  widget.Widget;
import  widget.Colored;
import  widget.RandomColor;
import  layout.GridLayout;

class SoundButtonsField extends GridLayout {

	var background : Colored;
	var displayed  : Bool;

	public function new(scene, logger) {
		super(scene, logger);

		this.displayed  = false;
		this.background = new Colored(
			RandomColor.withMask(
				0xF0F0F0, 0x809070));
	}

	override
	function redraw() {
		displayed = false;
		super.redraw();
	}

	override
	function display(queue) {
		if (!displayed) {
			logger.log('Drawing background.');
			background.place(
				this.x,     this.y,
				this.width, this.height,
				scene);
			displayed = true;
		}
		super.display(queue);
	}
}
