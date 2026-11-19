//! What layout and paint know of images (phase-6.md item 6.11): a map from each image to
//! its state, as 6.18's renderer pipeline fills it in as configs and pixels arrive.
//!
//! **This is the interface item 6.18 (the renderer pipeline) is to implement, and it is
//! defined here, minimally, as 6.11 needs it.** Nothing in this crate fetches, sniffs or
//! decodes; the pipeline does, and gives layout and paint an [`Images`]:
//!
//! - an `img` element is keyed by its **node id** in the arena (the pipeline has chosen its
//!   candidate from `srcset` and `sizes` and deduplicated downloads by URL, so two elements
//!   may share one image id);
//! - a CSS `background-image` is keyed by its **absolute URL** as a string, the form
//!   `clazel-style` computes it in ([`clazel_style::cascade::computed::BgImage::Url`],
//!   made absolute against its sheet by `cascade/urls.rs`).
//!
//! Each has an [`ImageStatus`]:
//!
//! - [`ImageStatus::Pending`]: no config yet (also what an unknown key is). An `img` is
//!   "an img element that represents nothing" for now: HTML §15.4.2: "a replaced element
//!   whose natural dimensions are 0", so 0 by 0 unless its attributes say otherwise
//!   (CSS 2.1 §10.3.2, §10.6.2).
//! - [`ImageStatus::Sized`]: the config has arrived (the decoder read the header: item
//!   6.4 to 6.8's `Config`), so layout can use the natural size, and paint draws nothing
//!   yet.
//! - [`ImageStatus::Ready`]: the pixels are uploaded under display list image id `id`
//!   (item 6.10: "image ids are a separate space below 2^16"); paint emits
//!   [`crate::paint::Item::Image`]s that refer to it.
//! - [`ImageStatus::Broken`]: the fetch or the decode failed, or the format is not
//!   supported. An `img` shows its `alt` text (`boxes/generate.rs`); a background layer
//!   paints nothing (CSS Backgrounds 3 §2.3: an image "that fails to download, or that
//!   cannot be displayed ... likewise counts as a layer but draws nothing").
//!
//! The **natural size** is in CSS pixels, which the pipeline computes from the image's
//! pixels and, for an `img` from a `srcset` density descriptor, the density (HTML
//! §4.8.4.3's density-corrected natural size); at density 1 it is the
//! pixel size. The **pixel size** is what a draw's source rectangle is expressed in
//! (item 6.10: source rectangles are in the image's pixels).
//!
//! Relayout: layout is a function of its inputs ([`crate::flow::layout_with_images`]), so
//! when a config arrives the pipeline updates the map and lays out again; batching those
//! relayouts to one per `Tick` is 6.18's.

use std::collections::HashMap;

/// A size in whole pixels (CSS pixels or image pixels, as the field says).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Dims {
    /// The width.
    pub width: u32,
    /// The height.
    pub height: u32,
}

/// What is known of one image.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ImageStatus {
    /// No config yet.
    #[default]
    Pending,
    /// The config is known.
    Sized {
        /// The natural size, in CSS pixels.
        natural: Dims,
    },
    /// The pixels are uploaded.
    Ready {
        /// The display list image id (item 6.10).
        id: u32,
        /// The natural size, in CSS pixels.
        natural: Dims,
        /// The size of the uploaded image, in image pixels.
        pixels: Dims,
    },
    /// It failed.
    Broken,
}

impl ImageStatus {
    /// The natural size, once the config is known.
    pub fn natural(&self) -> Option<Dims> {
        match *self {
            ImageStatus::Sized { natural } | ImageStatus::Ready { natural, .. } => Some(natural),
            ImageStatus::Pending | ImageStatus::Broken => None,
        }
    }
}

/// The images of a document, by `img` element and by background URL.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Images {
    elements: HashMap<usize, ImageStatus>,
    urls: HashMap<String, ImageStatus>,
}

impl Images {
    /// No image known: every `img` is pending.
    pub fn new() -> Images {
        Images::default()
    }

    /// Sets the status of the `img` element `node`.
    pub fn set_element(&mut self, node: usize, status: ImageStatus) {
        self.elements.insert(node, status);
    }

    /// Sets the status of the background image with absolute URL `url`.
    pub fn set_url(&mut self, url: &str, status: ImageStatus) {
        self.urls.insert(url.to_owned(), status);
    }

    /// The status of the `img` element `node`.
    pub fn element(&self, node: usize) -> ImageStatus {
        self.elements.get(&node).copied().unwrap_or_default()
    }

    /// The status of the background image with URL `url`.
    pub fn url(&self, url: &str) -> ImageStatus {
        self.urls.get(url).copied().unwrap_or_default()
    }
}
