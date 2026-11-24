// Twin of TESTING 18's `SLB-02-element` (corpus row SLB-02-element):
//
// let names: string[] = ["x".toString(), "yz".toString()];
// names[0] += pad(names.length());
// console.log(names);
//
// private function pad(n: isize): string { return "-".repeat(n); }
//
// Enrang accepts it and prints `['x--', 'yz']` (SPEC O6: a compound assignment to
// a non-Copy place reserves it until the store). rustc rejects `names[0] +=
// &pad(names.len())` with E0502 `cannot borrow `names` as immutable because it is
// also borrowed as mutable`, because its index borrow is not two-phase.

fn pad(n: isize) -> String {
    "-".repeat(n as usize)
}

fn main() {
    let mut names: Vec<String> = vec!["x".to_string(), "yz".to_string()];
    names[0] += &pad(names.len() as isize);
    println!("{:?}", names);
}
