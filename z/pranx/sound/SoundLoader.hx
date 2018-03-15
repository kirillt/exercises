package sound;

import  log.Logger;

import  widget.Button;
import  widget.RandomColor;

import  flash.media.Sound;

import  flash.events.Event;
import  flash.events.MouseEvent;

import  flash.net.FileReference;
import  flash.net.FileReferenceList;

class SoundLoader extends Button {

	var refs  : FileReferenceList;
	var files : Array<FileReference>;
	var queue : Array<FileReference>;

	var loadAction : FileReference -> Void;

	public function new(
		loadAction : FileReference -> Void,
		logger : Logger) {

		super(
			'Add files',
			RandomColor.withMask(
				0xF0F0F0, 0x80B080),
			logger);

		this.loadAction = loadAction;

		refs = new FileReferenceList();
		refs.addEventListener(
			Event.SELECT,
			onFilesSelect);
	}
	override
	function onClick(event : MouseEvent) {
		logger.log('SoundLoader was activated.');
		refs.browse();
	}

	function onFilesSelect(event : Event) {
		queue = new Array<FileReference>();
		files = refs.fileList;
		for (file in files) {
			queue.push(file);
		}
		logger.log('Selected:');
		logger.indent++;
		for (file in files) {
			logger.log(file.name);
		}
		logger.indent--;
		queue.reverse();
		logger.log('Loading:');
		logger.indent++;
		loadNext();
	}

	function fileLoaded(event : Event) {
		queue.pop();
		logger.logAppend(
			'\t\t\tDone.\t\t\t' +
			'(check: ' + event.target.name + ')');
		loadAction(event.target);
		loadNext();
	}

	function loadNext() {
		if (queue.length < 1) {
			logger.indent--;
			logger.log('Loading complete.');
			return;
		} else {
			var file = queue[queue.length - 1];

			logger.log(file.name);
			file.addEventListener(
				Event.COMPLETE,
				fileLoaded);
			file.load();
			return;
		}
	}
}
