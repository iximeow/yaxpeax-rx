//! decoding into a pre-existing instruction should not result in different outcomes compared to
//! decoding into a fresh instruction. if decoding succeeds, both outcomes should be equal.

#![no_main]
use libfuzzer_sys::fuzz_target;

use yaxpeax_arch::Decoder;

fuzz_target!(|data: &[u8]| {

    let decoders = [
        yaxpeax_rx::InstDecoder::v1(),
        yaxpeax_rx::InstDecoder::v2(),
        yaxpeax_rx::InstDecoder::v3(),
    ];

    let mut reused_inst = yaxpeax_rx::Instruction::default();

    for decoder in decoders {
        let mut words = yaxpeax_arch::U8Reader::new(data);
        // test decoding, may be ok or not, but should not panic
        if let Ok(()) = decoder.decode_into(&mut reused_inst, &mut words) {
            let mut words = yaxpeax_arch::U8Reader::new(data);
            let fresh_inst = decoder.decode(&mut words).expect("decoded before, can decode again");
            assert_eq!(reused_inst, fresh_inst);
        }
    }
});
