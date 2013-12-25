package log;

import  haxe.PosInfos;

import  flash.text.TextField;
import  flash.text.TextFieldAutoSize;

import  flash.display.Sprite;
import  flash.display.DisplayObject;
import  flash.display.DisplayObjectContainer;

import  widget.Widget;
import  widget.RandomColor;

class Logger implements Widget {

	public var indent : Int;

	var sprite    : TextField;
	var textField : TextField;
	var current   : DisplayObject;

	public function new() {
		sprite    = new TextField();
		textField = new TextField();

		current = textField;

		sprite.background           = true;
		sprite.backgroundColor      = RandomColor.withMask(0xF0F0F0, 0x102020);

		textField.multiline         = true;
		textField.mouseWheelEnabled = true;
		textField.background        = true;
		textField.textColor         = 0xFFFFFF;
		textField.autoSize          = TextFieldAutoSize.NONE;
		textField.backgroundColor   = RandomColor.withMask(0xF0F0F0, 0x102020);
	}

	public function hide(
		scene : DisplayObjectContainer) {

		scene.removeChild(textField);
		scene.addChild(sprite);
		current = sprite;
	}

	public function show(
		scene : DisplayObjectContainer) {

		scene.removeChild(sprite);
		scene.addChild(textField);
		current = textField;
	}

	public function place(
		x     : Float, y      : Float,
		width : Float, height : Float,
		scene : DisplayObjectContainer) {

		scene.addChild(current);
		current.x      = x - 0.5;
		current.y      = y - 0.5;
		current.width  = width  + 1;
		current.height = height + 1;
	}

	public function log(value : Dynamic, ?info : PosInfos) {
		var additional = info == null ? '' :
			info.fileName + ' : ' + info.lineNumber + '\t';

		for (i in 0...indent) {
			additional += '\t';
		}
		textField.appendText(
			'\n' + additional +
			value.toString());

		textField.scrollV = textField.maxScrollV;
	}
	public function logAppend(value : Dynamic) {
		textField.appendText(value);
	}
}
