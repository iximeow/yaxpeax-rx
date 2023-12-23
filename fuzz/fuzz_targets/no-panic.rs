#![no_main]
use libfuzzer_sys::fuzz_target;

use yaxpeax_arch::Decoder;

use std::fmt::Write;

fuzz_target!(|data: &[u8]| {

    let decoders = [
        yaxpeax_rx::InstDecoder::v1(),
        yaxpeax_rx::InstDecoder::v2(),
        yaxpeax_rx::InstDecoder::v3(),
    ];

    let mut rx_inst = yaxpeax_rx::Instruction::default();

    for decoder in decoders {
        let mut words = yaxpeax_arch::U8Reader::new(data);
        // test decoding, may be ok or not, but should not panic
        if let Ok(()) = decoder.decode_into(&mut rx_inst, &mut words) {
            write!(&mut String::new(), "{}", rx_inst).expect("formatting does not panic either");
        }
    }
});
