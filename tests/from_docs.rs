use yaxpeax_arch::Decoder;

// for "lazy" reasons i've found fairly few known-correct disassemblies to compare against. but
// what i have are checked here..

fn test_display(bytes: &[u8], text: &str) {
    let decoder = yaxpeax_rx::InstDecoder::default();
    let inst = decoder.decode(&mut yaxpeax_arch::U8Reader::new(bytes)).expect("decode succeeds");
    let rendered = format!("{}", inst);
    assert_eq!(rendered, text);
}

#[test]
fn from_support() {
    // this is from the image in
    // https://tool-support.renesas.com/autoupdate/support/onlinehelp/csp/V8.10.00/CS+.chm/DebugTool-RX.chm/Output/db_kinou_prog_disassemble.html
    // and more here
    // https://tool-support.renesas.com/autoupdate/support/onlinehelp/csp/V4.01.00/CS+.chm/DebugTool-RX.chm/Output/db_P_asm.html
    // which is wild but, hey.
    test_display(&[0x60, 0xc0], "sub #ch, r0");
    test_display(&[0xf8, 0x0a, 0x00, 0x10], "mov.l #1000h, [r0]");
    test_display(&[0xf9, 0x0a, 0x01, 0x78, 0x10], "mov.l #1078h, 4h[r0]");
    test_display(&[0x3e, 0x02, 0x00], "mov.l #0h, 8h[r0]");
    test_display(&[0x2e, 0x20], "bra.b $+0x20");
    test_display(&[0xa8, 0x81], "mov.l 8h[r0], r1");
    test_display(&[0xec, 0x02], "mov.l [r0], r2");
    test_display(&[0xe3, 0x21], "mov.l r1, [r2]");
    test_display(&[0x62, 0x11], "add #1h, r1");
    test_display(&[0xa0, 0x81], "mov.l r1, 8h[r0]");
}

#[test]
fn from_manual() {
    test_display(&[0x08], "bra.s $+0x8");
    test_display(&[0x09], "bra.s $+0x9");
    test_display(&[0x0a], "bra.s $+0xa");
    test_display(&[0x0b], "bra.s $+0x3");
    test_display(&[0x0c], "bra.s $+0x4");
    test_display(&[0x0d], "bra.s $+0x5");
    test_display(&[0x0e], "bra.s $+0x6");
    test_display(&[0x0f], "bra.s $+0x7");
}
