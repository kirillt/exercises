const canvas = document.getElementById('frame');
const gl = canvas.getContext('webgl');
let program;

const InitWebGL = function() {
    let VSText, FSText;
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
        });
};

const StartWebGL = function(vertexShaderText, fragmentShaderText) {
    if (!gl) {
        alert("Seems that your browser doesn't support WebGL");
        return;
    }

    canvas.width = gl.canvas.clientWidth;
    canvas.height = gl.canvas.clientHeight;

    gl.viewport(0, 0, gl.canvas.width, gl.canvas.height);

    function compile(typ, source) {
        let shader = gl.createShader(typ);

        gl.shaderSource(shader, source);
        gl.compileShader(shader);
        if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
            alert('Problem during vertex shader compilation');
            console.error('Shader error info: ', gl.getShaderInfoLog(shader));
        }

        return shader;
    }

    let vertexShader = compile(gl.VERTEX_SHADER, vertexShaderText);
    let fragmentShader = compile(gl.FRAGMENT_SHADER, fragmentShaderText);

    program = gl.createProgram();
    gl.attachShader(program, vertexShader);
    gl.attachShader(program, fragmentShader);

    gl.linkProgram(program);
    gl.validateProgram(program);

    if (!gl.getProgramParameter(program, gl.VALIDATE_STATUS)) {
        console.error('Error validating program ', gl.getProgramInfoLog(program));
        return;
    }

    draw();
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
    let result = [];
    for (i = 0; i < points.length; i++) {
    result.push({
            x: points[i].x + vector.x,
            y: points[i].y + vector.y
        });
    }
    return result;
};

const stretch = function(points, q) {
    let result = [];
    for (i = 0; i < points.length; i++) {
        result.push({
            x: points[i].x * q,
            y: points[i].y * q
        });
    }
    return result;	
};

const from_angles = function(segments) {
    let x = 0.0;
    let y = 0.0;
    let a = 0.0;

    let result = [];
    for (let i = 0; i < segments.length; i++) {
        let r = segments[i].length;

        a = a + segments[i].angle;
        x = x + r * Math.cos(a);
        y = y + r * Math.sin(a);

        result.push({x: x, y: y});
    }
    return result;
};

const polygon = function(n) {
    let radius = 1 / (2 * Math.sin(Math.PI / n));
    let figure = new Array({angle: 0, length: radius});

    let angle = 2 * Math.PI / n;
    for (let i = 0; i < n; i++) {
        figure.push({angle: angle, length: 1});
    }
    return from_angles(figure);
};

const triangulate_2d = function(contour) {
    let n = contour.length;
    if (n < 3) {
        alert("Can't triangulate " + n + " vertices");
        return undefined;
    }
    // if (n == 3) {
    	// return countour;
    // }

    let center = {x: 0, y: 0};
    for (let i = 0; i < n; i++) {
        center = {
            x: center.x + contour[i].x,
            y: center.y + contour[i].y
        };
    }
    center = {
        x: center.x / n,
        y: center.y / n
    };

    let result = [];
    for (let i = 0; i < n - 1; i++) {
        result = result.concat([contour[i], contour[i+1], center]);
    }
    result = result.concat([contour[n-1], contour[0], center]);

    return result;
};

const random_color = function() {
    return [Math.random(), Math.random(), Math.random()];
};

let n = 0;
let init = [];
{
    const figures = [
        move(stretch(polygon(9), 0.4), {x: -0.4, y: -0.4}),
        move(stretch(polygon(7), 0.4), {x: -0.3, y: -0.3}),
        move(stretch(polygon(5), 0.3), {x: -0.2, y: -0.2}),
        move(stretch(polygon(3), 0.2), {x: -0.1, y: -0.1}),
    ];

    let z = 0.0;
    const points = flatten(figures.map(f => {
        z = z - 0.05;
        const color = random_color();
        let triangulation = triangulate_2d(f);
        triangulation.forEach(p => {
            p.z = z;
            p.rgb = color;
        });
        return triangulation;
    }));

    n = points.length;

    init = flatten(points.map(p => [p.x, p.y, p.z].concat(p.rgb)));
}

let extra = [];

const draw = function() {
    const vertexBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, vertexBuffer);

    const points = init.concat(extra);
    let k = extra.length / 6;

    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(points), gl.STATIC_DRAW);

    let positionAttribLocation = gl.getAttribLocation(program, 'vertexPosition');
    gl.vertexAttribPointer(
        positionAttribLocation,
        3,
        gl.FLOAT,
        gl.FALSE,
        6 * Float32Array.BYTES_PER_ELEMENT,
        0
    );
    gl.enableVertexAttribArray(positionAttribLocation);

    let colorAttribLocation = gl.getAttribLocation(program, 'vertexColor');
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
    gl.drawArrays(gl.POINTS, 0, n + k);
    gl.drawArrays(gl.LINE_STRIP, 0, n + k);
};

canvas.onmousedown = function onmousedown(event) {
    const middle_X = gl.canvas.width / 2;
    const middle_Y = gl.canvas.height / 2;

    const rect = canvas.getBoundingClientRect();

    const x = (event.clientX - rect.left - middle_X) / middle_X;
    const y = (middle_Y - event.clientY + rect.top) / middle_Y;
    console.log("new point at (" + x + ", " + y + ")");

    extra = extra.concat([x, y, -0.1]);
    extra = extra.concat(random_color());
    draw();
};

document.addEventListener('DOMContentLoaded', function() {
    InitWebGL();
});
