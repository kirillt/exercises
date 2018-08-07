# Video-OPs
Simple video editor implemented in Rust and WebAssembly.

# Install Rust language

Open terminal, go to this folder and type:  

```bash
curl https://sh.rustup.rs -sSf | sh
rustup default nightly-2018-07-11
```

Make sure that you selected option to add ~/.cargo/bin into your $PATH.
If you missed it, you can do it manually:

```bash
echo "export PATH='~/.cargo/bin:$PATH'" >> ~/.bashrc
source ~/.bashrc
```

# Install necessary libraries

```bash
sudo apt install pkg-config openssl libssl-dev python nodejs vlc

```

# Fast start

```bash
rustup target add wasm32-unknown-unknown
rustup target add wasm32-unknown-emscripten
cargo install cargo-web
cargo web start
```  

Then go into your browser and open:

`http://localhost:8000`
