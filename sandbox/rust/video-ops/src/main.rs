#![feature(proc_macro)]
#![recursion_limit="128"]

#[macro_use]
extern crate stdweb;

use std::rc::Rc;
use std::cell::Cell;

use stdweb::traits::*;
use stdweb::unstable::TryInto;

use stdweb::web::{
    CanvasRenderingContext2d,
    document
};

use stdweb::web::event::{
    MouseDownEvent, MouseMoveEvent, MouseUpEvent
};

use stdweb::web::html_element::CanvasElement;

mod filters;
use filters::*;

macro_rules! query {
    ($selector:expr) => {
        document().query_selector($selector)
        .unwrap().unwrap()
        .try_into()
        .unwrap()
    }
}

#[derive(Debug, Clone, Copy)]
enum Region {
    Open(f64),
    Complete(f64, f64)
    //in percents
}

macro_rules! enclose {
    ( ($( $x:ident ),* ) $y:expr ) => {
        {
            $(let $x = $x.clone();)*
            $y
        }
    };
}

const COLOR_REGION_BACKGROUND: &str = "#0747af";
const COLOR_REGION_DRAGGING: &str = "#12ccf1";
const COLOR_REGION_SELECTED: &str = "#1368f2";
const COLOR_PLAYBACK_BACKGROUND: &str = "#3f28a8";
const COLOR_PLAYBACK_CURSOR: &str = "#dd1346";

fn main() {
    stdweb::initialize();

    {
        js! {
            window.wasm = {};
            window.wasm.grayscale = @{grayscale};
            window.wasm.negative = @{negative};
            window.wasm.sunset = @{sunset};
            window.wasm.forest = @{forest};
            window.wasm.longhorn = @{longhorn};
            window.wasm.blur = @{blur};
            window.wasm.goodMorning = @{good_morning};

            if (video.readyState >= 2) {
                frame.drawImage(video, 0.0, 0.0);
            }
        }
    }

    let region: Rc<Cell<Region>> = Rc::new(Cell::new(Region::Complete(0.0, 1.0)));

    {
        // Region selection
        let region_tl: CanvasElement = query!("#region_tl");

        let width = region_tl.offset_width() as f64;
        let height = region_tl.offset_height() as f64;

        region_tl.set_width(width as u32);
        region_tl.set_height(height as u32);

        let context: CanvasRenderingContext2d = region_tl
            .get_context()
            .unwrap();

        let fill_region = enclose!((context) move |color, from, to| {
            context.set_fill_style_color(color);
            context.fill_rect(from * width, 0.0, (to - from) * width, height);
        });

        let clear_selection = enclose!((fill_region) move || {
            fill_region(COLOR_REGION_BACKGROUND, 0.0, width);
            js! {
                region_from = 0;
                region_to = video.duration;
            }
        });

        clear_selection();

        let drag_selection = enclose!((fill_region, region) move |to| {
            if let Region::Open(from) = region.get() {
                fill_region(COLOR_REGION_DRAGGING, from, to);
            } else {
                panic!()
            }
        });

        let confirm_selection = enclose!((fill_region, region) move || {
            if let Region::Complete(from, to) = region.get() {
                let (from, to) = if from <= to {
                    (from, to)
                } else {
                    (to, from)
                };

                js! {
                    video.currentTime = video.duration * @{from};
                    region_from = Math.floor(@{from} * video.duration * 100) / 100;
                    region_to = Math.ceil(@{to} * video.duration * 100) / 100;
                }

                let color = if from != 0.0 || to != 1.0 {
                    COLOR_REGION_SELECTED
                } else {
                    COLOR_REGION_BACKGROUND
                };

                fill_region(color, from, to);
            } else {
                panic!()
            }
        });

        region_tl.add_event_listener(enclose!((region, clear_selection) move |event: MouseDownEvent| {
            clear_selection();
            region.set(Region::Open(event.offset_x() / width));
        }));

        region_tl.add_event_listener(enclose!((region, clear_selection) move |event: MouseMoveEvent| {
            if let Region::Open(_) = region.get() {
                clear_selection();
                drag_selection(event.offset_x() as f64 / width);
            }
        }));

        region_tl.add_event_listener(enclose!((region) move |event: MouseUpEvent| {
            if let Region::Open(from) = region.get() {
                let (from, to) = if event.offset_x() != from {
                    (from, event.offset_x() / width)
                } else {
                    (0.0, 1.0)
                };

                region.set(Region::Complete(from, to));
                confirm_selection();

                println!("region selected: {:?}", region.get());
            } else {
                panic!()
            }
        }));
    }

    {
        // Playback timeline
        let playback_tl: CanvasElement = query!("#playback_tl");

        let width = playback_tl.offset_width() as f64;
        let height = playback_tl.offset_height() as f64;

        playback_tl.set_width(width as u32);
        playback_tl.set_height(height as u32);

        let context: CanvasRenderingContext2d = playback_tl
            .get_context()
            .unwrap();

        let draw_line = enclose!((context) move |x| {
            context.set_fill_style_color(COLOR_PLAYBACK_BACKGROUND);
            context.fill_rect(0.0, 0.0, width, height);

            context.set_fill_style_color(COLOR_PLAYBACK_CURSOR);
            context.fill_rect(x, 0.0, 1.0, height);
        });

        let track_progress = enclose!((draw_line) move |percents| {
            draw_line(percents * width);
        });

        track_progress(0.0);

        playback_tl.add_event_listener(enclose!((region) move |event: MouseUpEvent| {
            if let Region::Complete(_, _) = region.get() {
                let percents = event.offset_x() / width;
                js! {
                    let length = region_to - region_from;
                    let time = region_from + length * @{percents};
                    video.currentTime = time;
                }
            } else {
                panic!()
            }
        }));

        js! {
            window.wasm.track = @{track_progress};
        }
    }

    stdweb::event_loop();
}