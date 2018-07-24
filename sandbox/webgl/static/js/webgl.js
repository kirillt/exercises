const canvas = document.getElementById('frame');
const gl = canvas.getContext('webgl');
let program;

function draw(time) {
    console.log(time);

    const vertexBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, vertexBuffer);

    time = (time % 360) / 360;
    console.log(time);
    let scene = window.wasm.scene(time);
    let n = scene.length / 6;
    for (let i = 0; i < scene.length; i += 6) {
        console.log("(" + scene[i] + ", " + scene[i+1] + ", " + scene[i+2] + ")");
    }

    gl.bufferData(gl.ARRAY_BUFFER, scene, gl.STATIC_DRAW);

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

    gl.drawArrays(gl.LINE_STRIP, 0, n);

    requestAnimationFrame(draw);
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

    requestAnimationFrame(draw);
}

document.addEventListener('DOMContentLoaded', function() {
    Rust.webgl_wasm.then(function () {
        InitWebGL();
    });
});
