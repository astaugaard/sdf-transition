use std::{borrow::BorrowMut, error::Error, fmt::Display, fs::File, mem};

use anyhow::{Context, Result};
use clap::Parser;
use gif::{Frame, Repeat};
use image::{GenericImageView, ImageReader, Luma, LumaA, Rgb, RgbImage};
use itertools::{chain, Itertools};
use rayon::prelude::*;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(short = '1', long)]
    image1: String,

    #[arg(short = '2', long)]
    image2: String,

    #[arg(short, long)]
    output: String,
}

#[derive(Debug)]
struct SDF {
    data: Vec<f32>,
}

#[derive(Debug)]
enum ProgramError {
    WidthsDifferent(usize, usize),
    HeightsDifferent(usize, usize),
}

impl Display for ProgramError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let _ = match self {
            ProgramError::WidthsDifferent(w1, w2) => write!(
                f,
                "widths of the two images are different image 1 width: {w1} image 2 width: {w2}"
            ),
            ProgramError::HeightsDifferent(h1, h2) => write!(
                f,
                "heights of the two images are different image 1 height: {h1} image 2 height: {h2}"
            ),
        };

        Ok(())
    }
}

impl Error for ProgramError {}

fn main() -> Result<()> {
    let Args {
        image1,
        image2,
        output,
    } = Args::parse();

    let image1 = ImageReader::open(image1)
        .with_context(|| "failed to read image1")?
        .decode()
        .with_context(|| "failed to decode image1")?
        .into_luma_alpha16();

    let image2 = ImageReader::open(image2)
        .with_context(|| "failed to read image2")?
        .decode()
        .with_context(|| "failed to decode image2")?
        .into_luma_alpha16();

    if image1.width() != image2.width() {
        return Result::Err(
            ProgramError::WidthsDifferent(image1.width() as usize, image2.width() as usize).into(),
        );
    }

    if image1.height() != image2.height() {
        return Result::Err(
            ProgramError::HeightsDifferent(image1.height() as usize, image2.height() as usize)
                .into(),
        );
    }

    let w = image1.width();
    let h = image2.height();

    // let sdf1 = generatesdf(&image1);

    //  // println!("sdf1 generated");

    //  // let sdfimg = rendersdf(&sdf1, w as usize);

    //  // sdfimg.save("./sdf1.png").unwrap();

    //  // let sdf2 = generatesdf(&image2);

    //  // println!("sdf2 generated");

    //  // let sdfimg2 = rendersdf(&sdf2, w as usize);

    //  // sdfimg2.save("./sdf2.png").unwrap();

    let mut output = File::create(output).with_context(|| "failed to create output file")?;

    let pallete = (0..=0xff).flat_map(|b| [b, b, b]).collect::<Vec<_>>();

    let mut output = gif::Encoder::new(&mut output, w as u16, h as u16, &pallete)
        .with_context(|| "failed to create encoder")?;

    output
        .set_repeat(Repeat::Infinite)
        .with_context(|| "failed te set repeat on gif")?;

    lerpsdfs(&image1, &image2, &mut output, 20).with_context(|| "failed to render gif")?;

    Ok(())
}

fn dist_to_color(dist: f32) -> Rgb<u8> {
    if dist.abs() <= 0.5 {
        let brightness = ((dist + 0.5) * 256.0) as u8;
        Rgb([brightness, brightness, brightness])
    } else if dist < 0.0 {
        if dist % 2.0 <= -0.9 {
            Rgb([0xff, 0xff, 0])
        } else {
            Rgb([0xff, 0, 0])
        }
    } else {
        // dist > 0.0
        if dist % 2.0 >= 0.9 {
            Rgb([0, 0xff, 0])
        } else {
            Rgb([0, 0, 0xff])
        }
    }
}

fn rendersdf(sdf1: &SDF, width: usize) -> RgbImage {
    let mut img = RgbImage::new(width as u32, (sdf1.data.len() / width) as u32);

    for (img, dist) in img.pixels_mut().zip(sdf1.data.iter()) {
        *img = dist_to_color(*dist);
    }

    img
}

fn lerpsdfs(
    image1: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>,
    image2: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>,
    output: &mut gif::Encoder<&mut File>,
    frames: u32,
) -> Result<()> {
    let mut changes_time = add_changes(&image1, &image2, 1.0 / frames as f32);

    // radsort because I can't be bothered to write a sort_by function thing (also probaly faster so idc)
    radsort::sort_by_key(&mut changes_time, |(t, _, _)| *t);

    let mut ct = 0.0;
    let dt = 1.0 / frames as f32;

    let buffer = decode_image(image1);

    let mut frame = Frame {
        width: image1.width() as u16,
        height: image1.height() as u16,
        buffer: std::borrow::Cow::Owned(buffer),
        ..Default::default()
    };

    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;

    let mut changes_time = changes_time.into_iter().peekable();

    while ct <= 1.0 {
        while changes_time
            .peek()
            .map(|(t, _, _)| *t <= ct)
            .unwrap_or(false)
        {
            let (_t, n, i) = changes_time.next().expect("just checked it was Some");
            frame.buffer.to_mut()[i] = n;
        }

        output
            .write_frame(&frame)
            .with_context(|| "failed to add frame to gif")?;

        ct += dt;
    }

    for (_t, n, i) in changes_time {
        frame.buffer.to_mut()[i] = n;
    }

    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;
    output
        .write_frame(&frame)
        .with_context(|| "failed to add frame to gif")?;

    Ok(())
}

fn decode_image(image1: &image::ImageBuffer<LumaA<u16>, Vec<u16>>) -> Vec<u8> {
    image1.pixels().map(|l| 0xff - (l[1] / 0x100) as u8).collect_vec()
}

// fn render(sdf1: SDF) -> Vec<u8> {
//     sdf1.data.iter().map(|f| result_pixel(*f)).collect()
// }

fn add_changes(
    image1: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>,
    image2: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>,
    step_size: f32,
) -> Vec<(f32, u8, usize)> {
    image1
        .par_enumerate_pixels()
        .enumerate()
        .zip(image2.par_pixels())
        .flat_map_iter(|((loc, (x, y, s)), e)| {
            add_changes_pixel(*s, *e, x, y, image1, image2, loc, step_size)
        })
        .collect::<Vec<_>>()

    // for ((i, s), e) in sdf1.data.iter().enumerate().zip(sdf2.data.iter()) {
    //     add_changes_pixel(*s, *e, changes_time, i, step_size);
    // }
}

// v = (1 - i) * s + i * e
// v = s - i * s + i * e
// v = s + (e - s) * i
// 0.5 = s + (e - s) * i
// (0.5 - s)/(e - s) = i

fn result_pixel(p: f32) -> u8 {
    // if p <= -0.5 {
    // 0x0
    // } else if p >= 0.5 {
    // 0xff
    // } else {
    // ((-p + 0.5) * 0xff as f32) as u8
    // }
    if p <= 0.0 {
        0x0
    } else {
        0xff
    }
}

fn lerp_pixel(s: f32, e: f32, i: f32) -> u8 {
    result_pixel(s + (e - s) * i)
}

fn add_changes_pixel(
    s: LumaA<u16>,
    e: LumaA<u16>,
    x: u32,
    y: u32,
    image1: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>,
    image2: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>,
    loc: usize,
    step_size: f32,
) -> Box<dyn Iterator<Item = (f32, u8, usize)>> {
    if e == s {
        return Box::new([].into_iter());
    }

    let s = distance(x, y, s, image1);
    let e = distance(x, y, e, image2);

    let crossings = [(0.5 - s) / (e - s), (-0.5 - s) / (e - s)]
        .into_iter()
        .filter(|a| 0.0 <= *a && *a <= 1.0)
        .collect::<Vec<_>>();

    match &crossings[..] {
        [c] => {
            if s.abs() <= 0.5 {
                Box::new(chain!(
                    (0..=((c / step_size).floor() as u32)).map(move |i| {
                        let i = i as f32 * step_size;
                        (i, lerp_pixel(s, e, i), loc)
                    }),
                    [(*c, result_pixel(e), loc)]
                ))
                // changes_time.push((*c, result_pixel(e), loc))

                // for i in 0..=((c / step_size).floor() as u32) {
                // let i = i as f32 * step_size;
                // changes_time.push((i, lerp_pixel(s, e, i), loc))
                // }
            } else {
                Box::new(
                    (((c / step_size).floor() as u32)..=((1.0 / step_size).floor() as u32)).map(
                        move |i| {
                            let i = i as f32 * step_size;
                            (i, lerp_pixel(s, e, i), loc)
                        },
                    ),
                )
                // for i in ((c / step_size).floor() as u32)..=((1.0 / step_size).floor() as u32) {
                // let i = i as f32 * step_size;
                // changes_time.push((i, lerp_pixel(s, e, i), loc))
                // }
                // changes_time.push((*c, result_pixel(e), loc))
            }
        }
        [a, b] => {
            let mut a = *a;
            let mut b = *b;

            if a >= b {
                mem::swap(&mut a, &mut b);
            }

            assert!(a <= b);

            Box::new(chain!(
                (((a / step_size).floor() as u32)..=((b / step_size).floor() as u32)).map(
                    move |i| {
                        let i = i as f32 * step_size;
                        (i, lerp_pixel(s, e, i), loc)
                    }
                ),
                [(b, result_pixel(e), loc)]
            ))

            // for i in ((a / step_size).floor() as u32)..=((b / step_size).floor() as u32) {
            // let i = i as f32 * step_size;
            // changes_time.push((i, lerp_pixel(s, e, i), loc))
            // }
            // changes_time.push((b, result_pixel(e), loc))
        }
        [] => Box::new([].into_iter()),
        _ => {
            dbg!(crossings);
            panic!("not possible")
        }
    }
}

fn generatesdf(image: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>) -> SDF {
    SDF {
        data: image
            .enumerate_pixels()
            // .par_bridge()
            .map(|(x, y, p)| distance(x, y, *p, image))
            .collect(),
    }
}

const NUM_ANGLES: u32 = 60;

fn distance(
    x: u32,
    y: u32,
    p: image::LumaA<u16>,
    image: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>,
) -> f32 {
    if p[1] < 0xffffu16 && 0x0000u16 < p[1] {
        return (p[1] as f32 - (0xffff as f32 / 2.0)) / 0xffff as f32;
    }

    (0..NUM_ANGLES)
        // .into_par_iter() // parrell here is slower
        .map(|i| {
            let a = i as f32 / NUM_ANGLES as f32 * 2.0 * std::f32::consts::PI;
            let dx = a.cos();
            let dy = a.sin();

            let d: f32 = raycast_distance(x, y, dx, dy, p[1], image, image.width(), image.height());
            d
        })
        .fold(f32::MAX, |a, b| if a.abs() < b.abs() { a } else { b })
        //.reduce(|| f32::MAX, |a, b| if a.abs() < b.abs() { a } else { b })
}

struct PixelRay {
    x: f32,
    y: f32,
    dx: f32,
    dy: f32,
    w: u32,
    h: u32,
    d: u32,
}

impl Iterator for PixelRay {
    type Item = (u32, u32, u32);

    fn next(&mut self) -> Option<Self::Item> {
        let cx = self.x.round() as i32;
        let cy = self.y.round() as i32;
        let cd = self.d;

        if cx >= self.w as i32 || cx < 0 || cy < 0 || cy >= self.h as i32 {
            return None;
        }

        self.d += 1;

        self.x += self.dx;
        self.y += self.dy;

        Some((cx as u32, cy as u32, cd))
    }
}

fn raycast_distance(
    x: u32,
    y: u32,
    dx: f32,
    dy: f32,
    p: u16,
    image: &image::ImageBuffer<image::LumaA<u16>, Vec<u16>>,
    w: u32,
    h: u32,
) -> f32 {
    for (x, y, d) in make_ray(x, y, dx, dy, w, h) {
        let np = image.get_pixel(x, y)[1];
        if np != p {
            return (if p == 0 { 1.0 } else { -1.0 })
                * (d as f32 + (np.abs_diff(p) as f32) / 0xffff as f32);
        }
    }

    f32::MAX
}

fn make_ray(x: u32, y: u32, dx: f32, dy: f32, w: u32, h: u32) -> PixelRay {
    PixelRay {
        x: x as f32,
        y: y as f32,
        dx,
        dy,
        w,
        h,
        d: 0,
    }
}
