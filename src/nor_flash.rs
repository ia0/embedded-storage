use crate::{iter::IterableByOverlaps, ReadStorage, Region, Storage};

/// Input bytes for read operation.
pub struct Bytes<'i, 'o> {
	input: &'i mut [u8],
	output: Option<&'o [u8]>,
}

impl<'i, 'o> Bytes<'i, 'o> {
	/// Prevents Drop to copy the content.
	pub fn no_copy(mut self) {
		self.output = None;
	}
}

impl<'i, 'o> core::ops::Deref for Bytes<'i, 'o> {
	type Target = [u8];

	fn deref<'a>(&'a self) -> &'a [u8] {
		match self.output {
			None => self.input,
			Some(x) => x,
		}
	}
}

impl<'i, 'o> From<&'i mut [u8]> for Bytes<'i, 'o> {
	fn from(input: &'i mut [u8]) -> Bytes<'i, 'o> {
		Bytes {
			input,
			output: None,
		}
	}
}

impl<'i, 'o> Drop for Bytes<'i, 'o> {
	fn drop(&mut self) {
		if let Some(output) = self.output {
			self.input.copy_from_slice(output);
		}
	}
}

#[test]
fn bytes_size() {
	assert_eq!(
		core::mem::size_of::<Bytes>(),
		2 * core::mem::size_of::<&mut [u8]>()
	);
}

#[test]
fn bytes_usage() {
	struct Flash<const N: usize> {
		storage: [u8; N],
	}
	const DIRECT: u32 = 0;
	const COPY: u32 = 1;
	impl<const N: usize> ReadNorFlash for Flash<N> {
		type Error = ();
		const READ_SIZE: usize = 1;
		fn read<'i, 'o>(
			&'o self,
			mode: u32,
			bytes: impl Into<Bytes<'i, 'o>>,
		) -> Result<Bytes<'i, 'o>, ()> {
			let mut bytes = bytes.into();
			if bytes.len() > N {
				return Err(());
			}
			match mode {
				DIRECT => bytes.output = Some(&self.storage[..bytes.len()]),
				COPY => bytes.input.copy_from_slice(&self.storage[..bytes.len()]),
				_ => unreachable!(),
			}
			Ok(bytes)
		}
		fn capacity(&self) -> usize {
			N
		}
	}

	const N: usize = 3;
	let storage = [0x53; N];
	let flash = Flash { storage };

	// Direct read and drop: copy to buffer.
	let mut buffer = [0; N];
	flash.read(DIRECT, &mut buffer[..]).unwrap();
	assert_eq!(buffer, storage);

	// Direct read and keep: no copy.
	let mut buffer = [0; N];
	let result = flash.read(DIRECT, &mut buffer[..]).unwrap();
	assert_eq!(*result, storage);
	result.no_copy();
	assert_eq!(buffer, [0; N]);

	// Copy read.
	let mut buffer = [0; N];
	flash.read(COPY, &mut buffer[..]).unwrap();
	assert_eq!(buffer, storage);

	// Multiple copy read.
	let mut buffer_a = [0; N];
	let mut buffer_b = [0; N];
	flash.read(COPY, &mut buffer_a[..]).unwrap();
	flash.read(COPY, &mut buffer_b[..]).unwrap();
	assert_eq!(buffer_a, storage);
	assert_eq!(buffer_b, storage);

	// Multiple direct read: requires read(&self) instead of read(&mut self).
	let mut buffer_a = [0; N];
	let mut buffer_b = [0; N];
	let result_a = flash.read(DIRECT, &mut buffer_a[..]).unwrap();
	let result_b = flash.read(DIRECT, &mut buffer_b[..]).unwrap();
	assert_eq!(*result_a, storage);
	assert_eq!(*result_b, storage);
	result_a.no_copy();
	result_b.no_copy();
	assert_eq!(buffer_a, [0; N]);
	assert_eq!(buffer_b, [0; N]);
}

/// Read only NOR flash trait.
pub trait ReadNorFlash {
	/// An enumeration of storage errors
	type Error;

	/// The minumum number of bytes the storage peripheral can read
	const READ_SIZE: usize;

	/// Read a slice of data from the storage peripheral, starting the read
	/// operation at the given address offset, and reading `bytes.len()` bytes.
	///
	/// This should throw an error in case `bytes.len()` will be larger than
	/// the peripheral end address.
	fn read<'i, 'o>(
		&'o self,
		offset: u32,
		bytes: impl Into<Bytes<'i, 'o>>,
	) -> Result<Bytes<'i, 'o>, Self::Error>;

	/// The capacity of the peripheral in bytes.
	fn capacity(&self) -> usize;
}

/// NOR flash trait.
pub trait NorFlash: ReadNorFlash {
	/// The minumum number of bytes the storage peripheral can write
	const WRITE_SIZE: usize;

	/// The minumum number of bytes the storage peripheral can erase
	const ERASE_SIZE: usize;

	/// Erase the given storage range, clearing all data within `[from..to]`.
	/// The given range will contain all 1s afterwards.
	///
	/// This should return an error if the range is not aligned to a proper
	/// erase resolution
	/// If power is lost during erase, contents of the page are undefined.
	/// `from` and `to` must both be multiples of `ERASE_SIZE` and `from` <= `to`.
	fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error>;

	/// If power is lost during write, the contents of the written words are undefined,
	/// but the rest of the page is guaranteed to be unchanged.
	/// It is not allowed to write to the same word twice.
	/// `offset` and `bytes.len()` must both be multiples of `WRITE_SIZE`.
	fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error>;
}

/// Marker trait for NorFlash relaxing the restrictions on `write`.
///
/// Writes to the same word twice are now allowed. The result is the logical AND of the
/// previous data and the written data. That is, it is only possible to change 1 bits to 0 bits.
///
/// If power is lost during write:
/// - Bits that were 1 on flash and are written to 1 are guaranteed to stay as 1
/// - Bits that were 1 on flash and are written to 0 are undefined
/// - Bits that were 0 on flash are guaranteed to stay as 0
/// - Rest of the bits in the page are guaranteed to be unchanged
pub trait MultiwriteNorFlash: NorFlash {}

struct Page {
	pub start: u32,
	pub size: usize,
}

impl Page {
	fn new(index: u32, size: usize) -> Self {
		Self {
			start: index * size as u32,
			size,
		}
	}

	/// The end address of the page
	const fn end(&self) -> u32 {
		self.start + self.size as u32
	}
}

impl Region for Page {
	/// Checks if an address offset is contained within the page
	fn contains(&self, address: u32) -> bool {
		(self.start <= address) && (self.end() > address)
	}
}

///
pub struct RmwNorFlashStorage<'a, S> {
	storage: S,
	merge_buffer: &'a mut [u8],
}

impl<'a, S> RmwNorFlashStorage<'a, S>
where
	S: NorFlash,
{
	/// Instantiate a new generic `Storage` from a `NorFlash` peripheral
	///
	/// **NOTE** This will panic if the provided merge buffer,
	/// is smaller than the erase size of the flash peripheral
	pub fn new(nor_flash: S, merge_buffer: &'a mut [u8]) -> Self {
		if merge_buffer.len() < S::ERASE_SIZE {
			panic!("Merge buffer is too small");
		}

		Self {
			storage: nor_flash,
			merge_buffer,
		}
	}
}

impl<'a, S> ReadStorage for RmwNorFlashStorage<'a, S>
where
	S: ReadNorFlash,
{
	type Error = S::Error;

	fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
		// Nothing special to be done for reads
		self.storage.read(offset, bytes)?;
		Ok(())
	}

	fn capacity(&self) -> usize {
		self.storage.capacity()
	}
}

impl<'a, S> Storage for RmwNorFlashStorage<'a, S>
where
	S: NorFlash,
{
	fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
		// Perform read/modify/write operations on the byte slice.
		let last_page = self.storage.capacity() / S::ERASE_SIZE;

		// `data` is the part of `bytes` contained within `page`,
		// and `addr` in the address offset of `page` + any offset into the page as requested by `address`
		for (data, page, addr) in (0..last_page as u32)
			.map(move |i| Page::new(i, S::ERASE_SIZE))
			.overlaps(bytes, offset)
		{
			let offset_into_page = addr.saturating_sub(page.start) as usize;

			self.storage
				.read(page.start, &mut self.merge_buffer[..S::ERASE_SIZE])?;

			// If we cannot write multiple times to the same page, we will have to erase it
			self.storage.erase(page.start, page.end())?;
			self.merge_buffer[..S::ERASE_SIZE]
				.iter_mut()
				.skip(offset_into_page)
				.zip(data)
				.for_each(|(byte, input)| *byte = *input);
			self.storage
				.write(page.start, &self.merge_buffer[..S::ERASE_SIZE])?;
		}
		Ok(())
	}
}

///
pub struct RmwMultiwriteNorFlashStorage<'a, S> {
	storage: S,
	merge_buffer: &'a mut [u8],
}

impl<'a, S> RmwMultiwriteNorFlashStorage<'a, S>
where
	S: MultiwriteNorFlash,
{
	/// Instantiate a new generic `Storage` from a `NorFlash` peripheral
	///
	/// **NOTE** This will panic if the provided merge buffer,
	/// is smaller than the erase size of the flash peripheral
	pub fn new(nor_flash: S, merge_buffer: &'a mut [u8]) -> Self {
		if merge_buffer.len() < S::ERASE_SIZE {
			panic!("Merge buffer is too small");
		}

		Self {
			storage: nor_flash,
			merge_buffer,
		}
	}
}

impl<'a, S> ReadStorage for RmwMultiwriteNorFlashStorage<'a, S>
where
	S: ReadNorFlash,
{
	type Error = S::Error;

	fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
		// Nothing special to be done for reads
		self.storage.read(offset, bytes)?;
		Ok(())
	}

	fn capacity(&self) -> usize {
		self.storage.capacity()
	}
}

impl<'a, S> Storage for RmwMultiwriteNorFlashStorage<'a, S>
where
	S: MultiwriteNorFlash,
{
	fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
		// Perform read/modify/write operations on the byte slice.
		let last_page = self.storage.capacity() / S::ERASE_SIZE;

		// `data` is the part of `bytes` contained within `page`,
		// and `addr` in the address offset of `page` + any offset into the page as requested by `address`
		for (data, page, addr) in (0..last_page as u32)
			.map(move |i| Page::new(i, S::ERASE_SIZE))
			.overlaps(bytes, offset)
		{
			let offset_into_page = addr.saturating_sub(page.start) as usize;

			self.storage
				.read(page.start, &mut self.merge_buffer[..S::ERASE_SIZE])?;

			let rhs = &self.merge_buffer[offset_into_page..S::ERASE_SIZE];
			let is_subset = data.iter().zip(rhs.iter()).all(|(a, b)| *a & *b == *a);

			// Check if we can write the data block directly, under the limitations imposed by NorFlash:
			// - We can only change 1's to 0's
			if is_subset {
				// Use `merge_buffer` as allocation for padding `data` to `WRITE_SIZE`
				let offset = addr as usize % S::WRITE_SIZE;
				let aligned_end = data.len() % S::WRITE_SIZE + offset + data.len();
				self.merge_buffer[..aligned_end].fill(0xff);
				self.merge_buffer[offset..offset + data.len()].copy_from_slice(data);
				self.storage
					.write(addr - offset as u32, &self.merge_buffer[..aligned_end])?;
			} else {
				self.storage.erase(page.start, page.end())?;
				self.merge_buffer[..S::ERASE_SIZE]
					.iter_mut()
					.skip(offset_into_page)
					.zip(data)
					.for_each(|(byte, input)| *byte = *input);
				self.storage
					.write(page.start, &self.merge_buffer[..S::ERASE_SIZE])?;
			}
		}
		Ok(())
	}
}
