use std::{borrow::BorrowMut, error::Error, fmt::Display, fs::File, mem};

use anyhow::{Context, Result};
use clap::Parser;
use gif::{Frame, Repeat};
use image::{GenericImageView, ImageReader, Luma};

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
        .to_luma16();

    let image2 = ImageReader::open(image2)
        .with_context(|| "failed to read image2")?
        .decode()
        .with_context(|| "failed to decode image2")?
        .to_luma16();

    if image1.width() != image2.width() {
        return Result::Err(
            ProgramError::WidthsDifferent(image1.width() as usize, image2.width() as usize).into(),
        );
    }

    if image1.height() != image2.height() {
        return Result::Err(
            ProgramError::WidthsDifferent(image1.height() as usize, image2.height() as usize)
                .into(),
        );
    }

    let w = image1.width();
    let h = image2.height();

    let sdf1 = generatesdf(&image1);

    let sdf2 = generatesdf(&image2);

    let mut output = File::create(output).with_context(|| "failed to create output file")?;

    let pallete = (0..=0xff).flat_map(|b| [b, b, b]).collect::<Vec<_>>();

    let mut output = gif::Encoder::new(&mut output, w as u16, h as u16, &pallete)
        .with_context(|| "failed to create encoder")?;

    output
        .set_repeat(Repeat::Infinite)
        .with_context(|| "failed te set repeat on gif")?;

    lerpsdfs(sdf1, sdf2, &mut output, 60, w, h).with_context(|| "failed to render gif")?;

    Ok(())
}

fn lerpsdfs(
    sdf1: SDF,
    sdf2: SDF,
    output: &mut gif::Encoder<&mut File>,
    frames: u32,
    w: u32,
    h: u32,
) -> Result<()> {
    let mut changes_time = Vec::new();

    add_changes(&sdf1, &sdf2, &mut changes_time, 1.0 / frames as f32);

    // radsort because I can't be bothered to write a sort_by function thing (also probaly faster so idc)
    radsort::sort_by_key(&mut changes_time, |(t, _, _)| *t);

    let mut ct = 0.0;
    let dt = 1.0 / frames as f32;

    let buffer = render(sdf1);

    let mut frame = Frame {
        width: w as u16,
        height: h as u16,
        buffer: std::borrow::Cow::Owned(buffer),
        ..Default::default()
    };

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

    Ok(())
}

fn render(sdf1: SDF) -> Vec<u8> {
    sdf1.data.iter().map(|f| result_pixel(*f)).collect()
}

fn add_changes(
    sdf1: &SDF,
    sdf2: &SDF,
    changes_time: &mut Vec<(f32, u8, usize)>,
    step_size: f32,
) {
    for ((i, s), e) in sdf1.data.iter().enumerate().zip(sdf2.data.iter()) {
        add_changes_pixel(*s, *e, changes_time, i, step_size);
    }
}

// v = (1 - i) * s + i * e
// v = s - i * s + i * e
// v = s + (e - s) * i
// 0.5 = s + (e - s) * i
// (0.5 - s)/(e - s) = i

fn result_pixel(p: f32) -> u8 {
    if p <= -0.5 {
        0x0
    } else if p >= 0.5 {
        0xff
    } else {
        ((p + 0.5) * 0xff as f32) as u8
    }
}

fn lerp_pixel(s: f32, e: f32, i: f32) -> u8 {
    result_pixel(s + (e - s) * i)
}

fn add_changes_pixel(
    s: f32,
    e: f32,
    changes_time: &mut Vec<(f32, u8, usize)>,
    loc: usize,
    step_size: f32,
) {
    if result_pixel(e) == result_pixel(s) {
        return;
    }

    let crossings = [(0.5 - s) / (e - s), (-0.5 - s) / (e - s)]
        .into_iter()
        .filter(|a| 0.0 <= *a && *a <= 1.0)
        .collect::<Vec<_>>();

    match &crossings[..] {
        [c] => {
            if s.abs() <= 0.5 {
                for i in 0..=((c / step_size).floor() as u32) {
                    let i = i as f32 * step_size;
                    changes_time.push((i, lerp_pixel(s, e, i), loc))
                }
                changes_time.push((*c, result_pixel(e), loc))
            } else {
                for i in ((c / step_size).floor() as u32)..=((1.0 / step_size).floor() as u32) {
                    let i = i as f32 * step_size;
                    changes_time.push((i, lerp_pixel(s, e, i), loc))
                }
                changes_time.push((*c, result_pixel(e), loc))
            }
        }
        [a, b] => {
            let mut a = *a;
            let mut b = *b;

            if b >= a {
                mem::swap(&mut a, &mut b);
            }

            for i in ((a / step_size).floor() as u32)..=((b / step_size).floor() as u32) {
                let i = i as f32 * step_size;
                changes_time.push((i, lerp_pixel(s, e, i), loc))
            }
            changes_time.push((b, result_pixel(e), loc))
        }
        _ => panic!("not possible"),
    }
}

fn generatesdf(image: &image::ImageBuffer<image::Luma<u16>, Vec<u16>>) -> SDF {
    SDF {
        data: image
            .enumerate_pixels()
            .map(|(x, y, p)| distance(x, y, *p, image))
            .collect(),
    }
}

const NUM_ANGLES: u32 = 60;

fn distance(
    x: u32,
    y: u32,
    p: Luma<u16>,
    image: &image::ImageBuffer<image::Luma<u16>, Vec<u16>>,
) -> f32 {
    if p[0] < 0xffff && 0x0000 < p[0] {
        return (p[0] as f32 - 0xffff as f32 / 2.0) / 0xffff as f32;
    }

    (0..NUM_ANGLES)
        .map(|i| {
            let a = i as f32 / NUM_ANGLES as f32;
            let dx = a.cos();
            let dy = a.sin();

            let d: f32 = raycast_distance(x, y, dx, dy, p[0], image, image.width(), image.height());
            d
        })
        .fold(f32::MAX, |a, b| a.min(b))
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
        let cx = self.x.round();
        let cy = self.y.round();
        let cd = self.d;

        if self.x > (self.w as f32 - 0.5)
            || self.x < 0.0
            || self.y < 0.0
            || self.y > (self.h as f32 - 0.5)
        {
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
    image: &image::ImageBuffer<image::Luma<u16>, Vec<u16>>,
    w: u32,
    h: u32,
) -> f32 {
    let mut lastdist = 0;
    for (x, y, d) in make_ray(x, y, dx, dy, w, h) {
        let np = image.get_pixel(x, y)[0];
        lastdist = d;
        if np != p {
            return (if p == 0 { -1.0 } else { 1.0 }) * (d as f32 + np.abs_diff(p) as f32);
        }
    }

    lastdist as f32
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
