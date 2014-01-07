package widget;

import  log.Logger;

import  haxe.PosInfos;

import  flash.text.TextField;
import  flash.text.TextFormatAlign;
import  flash.text.TextFieldAutoSize;

import  flash.events.Event;
import  flash.events.MouseEvent;

import  flash.display.Sprite;
import  flash.display.DisplayObjectContainer;

class Button implements Widget {

	var logger : Logger;
	var text   : TextField;

	public function new(
		text : String, color : Int,
		logger : Logger) {

		this.logger = logger;

		this.text = new TextField();

		this.text.text              = text;
		this.text.background        = true;
		this.text.selectable        = false;
		this.text.multiline         = false;
		this.text.mouseWheelEnabled = false;
		this.text.backgroundColor   = color;
		this.text.textColor         = 0xFFFFFF;
		this.text.autoSize          = TextFieldAutoSize.NONE;

		var format = this.text.getTextFormat();
		format.align = TextFormatAlign.CENTER;
		this.text.setTextFormat(format);

		this.text.addEventListener(
			Event.ADDED_TO_STAGE,
			onAddedToStage);
	}

	public function place(
		x     : Float, y      : Float,
		width : Float, height : Float,
		scene : DisplayObjectContainer) {

		scene.addChild(text);

		text.x      = x;
		text.y      = y;
		text.width  = width;
		text.height = height;
	}

	function onAddedToStage(event : Event) {
		event.target.addEventListener(
			MouseEvent.CLICK,
			onClick);
	}
	function onClick(event : MouseEvent) {
		logger.log('Button ' + text.toString() + 'was clicked.');
	}
}
