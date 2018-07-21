var canvas = document.getElementById('frame');
var gl = canvas.getContext('webgl');
var program;

const InitWebGL = function() {
	var VSText, FSText;
	loadTextResource('shaders/vertexShader.glsl')
	.then(function(result) {
		VSText = result;
		return loadTextResource('shaders/fragmentShader.glsl');
	})
	.then(function(result) {
		FSText = result;
		return StartWebGL(VSText, FSText);
	})
	.catch(function(error) {
		alert('Error while loading resources');
		console.error(error);
	})
}

const StartWebGL = function(vertexShaderText, fragmentShaderText) {
	if (!gl) {
		alert("Seems that your browser doesn't support WebGL");
		return;
	}

	canvas.width = gl.canvas.clientWidth;
	canvas.height = gl.canvas.clientHeight;

	gl.viewport(0, 0, gl.canvas.width, gl.canvas.height);

	function compile(typ, source) {
		var shader = gl.createShader(typ);

		gl.shaderSource(shader, source);
		gl.compileShader(shader);
		if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
			alert('Problem during vertex shader compilation');
			console.error('Shader error info: ', gl.getShaderInfoLog(shader));
		}

		return shader;
	}

	var vertexShader = compile(gl.VERTEX_SHADER, vertexShaderText);
	var fragmentShader = compile(gl.FRAGMENT_SHADER, fragmentShaderText);

	program = gl.createProgram();
	gl.attachShader(program, vertexShader);
	gl.attachShader(program, fragmentShader);

	gl.linkProgram(program);
	gl.validateProgram(program);

	if (!gl.getProgramParameter(program, gl.VALIDATE_STATUS)) {
		console.error('Error validating program ', gl.getProgramInfoLog(program));
		return;
	}

	draw()
};

const flatten = function(arr, result = []) {
  for (let i = 0, length = arr.length; i < length; i++) {
    const value = arr[i];
    if (Array.isArray(value)) {
      flatten(value, result);
    } else {
      result.push(value);
    }
  }
  return result;
};

const move = function(points, vector) {
    var result = new Array();
    for (i = 0; i < points.length; i++) {
    	result.push({
    		x: points[i].x + vector.x,
    		y: points[i].y + vector.y
    	});
    }
    return result;
}

const stretch = function(points, q) {
    var result = new Array();
    for (i = 0; i < points.length; i++) {
    	result.push({
    		x: points[i].x * q,
    		y: points[i].y * q
    	});
    }
    return result;	
}

const triangulate_2d = function(contour) {
	var n = contour.length;
	if (n < 3) {
		alert("Can't triangulate " + n + " vertices");
		return undefined;
	}
    // if (n == 3) {
    	// return countour;
    // }

	var center = {x: 0, y: 0};
    for (i = 0; i < n; i++) {
    	center = {
    		x: center.x + contour[i].x,
    		y: center.y + contour[i].y
    	};
    }
    center = {
    	x: center.x / n,
    	y: center.y / n
    };

    var result = new Array();
    for (i = 0; i < n - 1; i++) {
    	result = result.concat([contour[i], contour[i+1], center]);
    }
    result = result.concat([contour[n-1], contour[0], center]);

    return result;
};

var extra = [];

const draw = function() {
	var vertexBuffer = gl.createBuffer();
	gl.bindBuffer(gl.ARRAY_BUFFER, vertexBuffer);

    var figure = stretch(
    	move([{x: 0, y: 0}, {x: 1, y: 0}, {x: 1, y: 1}, {x: 0, y: 1}],
    		{x: -0.5, y: -0.5}),
    	0.7);

	var points = triangulate_2d(figure);
	// var points = figure;
	var n = points.length;
	var k = extra.length / 6;
	points = flatten(points.map(p => [p.x, p.y, 0.0,   0.0,0.0,1.0]));
                                    //  x    y    z      r   g   b
    points = points.concat(extra);

	gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(points), gl.STATIC_DRAW);

	var positionAttribLocation = gl.getAttribLocation(program, 'vertexPosition');
	gl.vertexAttribPointer(
		positionAttribLocation,
		3,
		gl.FLOAT,
		gl.FALSE,
		6 * Float32Array.BYTES_PER_ELEMENT,
		0 * Float32Array.BYTES_PER_ELEMENT
	);
	gl.enableVertexAttribArray(positionAttribLocation);

	var colorAttribLocation = gl.getAttribLocation(program, 'vertexColor');
	gl.vertexAttribPointer(
		colorAttribLocation,
		3,
		gl.FLOAT,
		gl.FALSE,
		6 * Float32Array.BYTES_PER_ELEMENT,
		3 * Float32Array.BYTES_PER_ELEMENT
	);
	gl.enableVertexAttribArray(colorAttribLocation);


	gl.clearColor(0.75, 0.9, 1.0, 1.0);
	gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
	gl.enable(gl.DEPTH_TEST);
	gl.useProgram(program);

    // gl.POINTS: Draws a single dot.
    // gl.LINE_STRIP: Draws a straight line to the next vertex.
    // gl.LINE_LOOP: Draws a straight line to the next vertex, and connects the last vertex back to the first.
    // gl.LINES: Draws a line between a pair of vertices.
    // gl.TRIANGLE_STRIP
    // gl.TRIANGLE_FAN
    // gl.TRIANGLES: Draws a triangle for a group of three vertices.
	gl.drawArrays(gl.TRIANGLES, 0, n + k);
}

canvas.onmousedown = function onmousedown(event) {
	var middle_X = gl.canvas.width / 2;
	var middle_Y = gl.canvas.height / 2;

	var rect = canvas.getBoundingClientRect();

	var x = (event.clientX - rect.left - middle_X) / middle_X;
	var y = (middle_Y - event.clientY + rect.top) / middle_Y;
	console.log("new point at (" + x + ", " + y + ")");

	extra.push(x, y, -0.1, 1.0,0.0,0.0);
	draw();
};

document.addEventListener('DOMContentLoaded', function() {
	InitWebGL();
});
