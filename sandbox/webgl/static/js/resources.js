var loadTextResource = function(url) {
	return new Promise(function (resolve, reject) {
		var request = new XMLHttpRequest();
		request.open('GET', url, true);
		request.onload = function() {
			if (request.status >= 200 && request.status < 300) {
				resolve(request.responseText);
			} else {
				reject('HTTP status: ' + request.status + ' on ' + url);
			}
		};
		request.send();
	});
}