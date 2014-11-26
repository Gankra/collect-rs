#[cfg(test)]
mod bench_old {
    use test::Bencher;
    use test;

    use std::collections::RingBuf;

    fn bench_push_x(b: &mut Bencher, x: u32) {
        b.iter(|| {
            let mut buf = RingBuf::new();
            for i in range(0, x){
                buf.push_back(i);
            }
            for i in range(0, x){
                buf.push_front(i);
            }
            buf
        });
    }

    fn bench_push_cap_x(b: &mut Bencher, x: u32) {
        b.iter(|| {
            let mut buf = RingBuf::with_capacity((x * 2) as uint);
            for i in range(0, x){
                buf.push_back(i);
            }
            for i in range(0, x){
                buf.push_front(i);
            }
            buf
        });
    }

    #[bench]
    fn bench_push_10(b: &mut Bencher) { bench_push_x(b, 10) }
    #[bench]
    fn bench_push_100(b: &mut Bencher) { bench_push_x(b, 100) }
    #[bench]
    fn bench_push_10000(b: &mut Bencher) { bench_push_x(b, 10000) }

    #[bench]
    fn bench_push_cap_10(b: &mut Bencher) { bench_push_cap_x(b, 10) }
    #[bench]
    fn bench_push_cap_100(b: &mut Bencher) { bench_push_cap_x(b, 100) }
    #[bench]
    fn bench_push_cap_10000(b: &mut Bencher) { bench_push_cap_x(b, 10000) }
}

#[cfg(test)]
mod bench_faux {
    use test::Bencher;
    use test;

    use proto::ring_buf_faux::RingBuf;

    fn bench_push_x(b: &mut Bencher, x: u32) {
        b.iter(|| {
            let mut buf = RingBuf::new();
            for i in range(0, x){
                buf.push_back(i);
            }
            for i in range(0, x){
                buf.push_front(i);
            }
            buf
        });
    }

    fn bench_push_cap_x(b: &mut Bencher, x: u32) {
        b.iter(|| {
            let mut buf = RingBuf::with_capacity((x * 2) as uint);
            for i in range(0, x){
                buf.push_back(i);
            }
            for i in range(0, x){
                buf.push_front(i);
            }
            buf
        });
    }

    #[bench]
    fn bench_push_10(b: &mut Bencher) { bench_push_x(b, 10) }
    #[bench]
    fn bench_push_100(b: &mut Bencher) { bench_push_x(b, 100) }
    #[bench]
    fn bench_push_10000(b: &mut Bencher) { bench_push_x(b, 10000) }

    #[bench]
    fn bench_push_cap_10(b: &mut Bencher) { bench_push_cap_x(b, 10) }
    #[bench]
    fn bench_push_cap_100(b: &mut Bencher) { bench_push_cap_x(b, 100) }
    #[bench]
    fn bench_push_cap_10000(b: &mut Bencher) { bench_push_cap_x(b, 10000) }
}