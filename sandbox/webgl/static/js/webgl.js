const canvas = document.getElementById('frame');
const gl = canvas.getContext('webgl');
let program;

let points;
function initialize() {
    const figures = [
        move_2d(stretch_2d(polygon(300), {x: 0.5, y: 0.5}), {x: -0.5, y: -0.5}),
        move_2d(stretch_2d(polygon(400), {x: 0.5, y: 0.5}), {x: -0.3, y: -0.3}),
        move_2d(stretch_2d(polygon(500), {x: 0.5, y: 0.5}), {x: -0.1, y: -0.1}),
        move_2d(stretch_2d(polygon(600), {x: 0.5, y: 0.5}), {x:  0.1, y:  0.1}),
        move_2d(stretch_2d(polygon(700), {x: 0.5, y: 0.5}), {x:  0.3, y:  0.3}),
        move_2d(stretch_2d(polygon(800), {x: 0.5, y: 0.5}), {x:  0.5, y:  0.5})
    ];

    let n = figures.length;

    const js_start = performance.now();
    const js_result = figures.map((figure, i) => {
        const rgb = random_color();
        return triangulate_2d(figure, i / n, rgb);
    });
    console.log("js time: " + (performance.now() - js_start));

    const wasm_start = performance.now();
    const wasm_result = figures.map((figure, i) => {
        const rgb = random_color();
        return window.wasm.triangulate_2d(new Float32Array(figure), i / n, rgb[0], rgb[1], rgb[2]);
    });
    console.log("wasm time: " + (performance.now() - wasm_start));

    points = concatenate(Float32Array, wasm_result);
}

function draw() {
    const vertexBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, vertexBuffer);

    let n = points.length / 6;

    gl.bufferData(gl.ARRAY_BUFFER, points, gl.STATIC_DRAW);

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

    gl.drawArrays(gl.TRIANGLES, 0, n);
}

function InitWebGL() {
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
}

function StartWebGL(vertexShaderText, fragmentShaderText) {
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
}

document.addEventListener('DOMContentLoaded', function() {
    Rust.webgl_wasm.then(function () {
        initialize();
        InitWebGL();
    });
});
