package sound;

import  log.Logger;

import  widget.Button;

import  flash.events.Event;
import  flash.events.MouseEvent;

import  flash.net.FileReference;

import  flash.media.Sound;
import  flash.media.SoundChannel;

class SoundButton extends Button {

	var soundLogger : Logger;
	var channel     : SoundChannel;
	var color       : Int;
	var sound       : Sound;
	var file        : FileReference;

	public function new(
		file           : FileReference,
		color          : Int,
		soundLogger    : Logger,
		graphicsLogger : Logger) {

		super(file.name, color, graphicsLogger);

		this.sound       = new Sound();
		this.color       = color;
		this.file        = file;
		this.soundLogger = soundLogger;

		var data   = file.data;
		sound.loadCompressedDataFromByteArray(
			data, data.bytesAvailable);
	}

	function cutName(text : String) {
		var splitted = text.split('.mp3');
		return splitted[0];
	}

	override
	function onClick(event : MouseEvent) {
//		logger.log('SoundButton was clicked.');
		if (channel == null) {
			channel = sound.play();
			text.backgroundColor = color ^ 0xFFFFFF;
//			soundLogger.log(file.name + ' started.');
			channel.addEventListener(
				Event.SOUND_COMPLETE,
				onComplete);
		} else {
			onComplete(event);
		}
	}

	function onComplete(event : Event) {
		channel.stop();
		channel = null;
		text.backgroundColor = color;
//		soundLogger.log(file.name + ' stopped.');
	}
}
