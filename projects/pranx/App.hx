package;

import  log.Logger;

import  flash.Lib;
import  flash.display.StageScaleMode;

import  widget.Empty;
import  widget.Colored;
import  widget.RandomColor;

import  layout.Matrix;
import  layout.GridLayout;

import  flash.net.FileReference;

import  sound.SoundLoader;
import  sound.SoundButton;
import  sound.SoundButtonsField;

class App {
	public static function main() {
		var stage = Lib.current.stage;
		stage.scaleMode = NO_SCALE;

		var graphicsLogger = new Logger();
		var soundLogger    = new Logger();

		var innerLayout = new SoundButtonsField(
			stage, graphicsLogger);
		var outerLayout = new GridLayout(
			stage, graphicsLogger);

		outerLayout.x      = 0;
		outerLayout.y      = 0;
		outerLayout.width  = stage.stageWidth;
		outerLayout.height = stage.stageHeight;

		innerLayout.addWidget(0, 0, 1,    1,  new Empty());
		innerLayout.addWidget(1, 0, 799,  1,  new Empty());
		innerLayout.addWidget(0, 1, 1,  249,  new Empty());

		var loadAction = function(file : FileReference) {
			var sound = new SoundButton(
				file,
				RandomColor.withMask(
					0xF0F0F0, 0xA03030),
				soundLogger, graphicsLogger);

			innerLayout.setAutomaticallyBySizeWithMargin(
				100, 10, 2, 2, sound);
			innerLayout.displayNew();

			graphicsLogger.log('SoundButton created.');
		}

		outerLayout.addWidget(
			0,0,10,5,
			new SoundLoader(
				loadAction,
				soundLogger));

		outerLayout.addWidget(
			10,0,90,5,
			new Colored(
				RandomColor.withMask(
					0xF0F0F0, 0x304050)));

		outerLayout.addWidget(
			0 ,170,50,30, soundLogger);
		outerLayout.addWidget(
			50,170,50,30, graphicsLogger);

		outerLayout.setAutomatically(
			0,5, innerLayout);

		outerLayout.displayNew();
	}
}
