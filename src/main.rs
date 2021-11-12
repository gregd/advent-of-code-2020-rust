#![allow(dead_code)]

use std::collections::{HashMap, HashSet, VecDeque};
use std::collections::hash_map::DefaultHasher;
use std::convert::TryInto;
use std::fmt::Debug;
use std::fs;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::ops::Range;
use std::str::FromStr;

use regex::Regex;

fn main() {
    assert_eq!(day_0(), 0);
    assert_eq!(day_1(), 1013211);
    assert_eq!(day_1b(), 13891280);
    assert_eq!(day_2(), 477);
    assert_eq!(day_2b(), 686);
    assert_eq!(day_3(), 198);
    assert_eq!(day_3b(), 5140884672);
    assert_eq!(day_4(), 247);
    assert_eq!(day_4b(), 145);
    assert_eq!(day_5(), 959);
    assert_eq!(day_5b(), 527);
    assert_eq!(day_6(), 6170);
    assert_eq!(day_6b(), 2947);
    assert_eq!(day_7(), 278);
    assert_eq!(day_7b(), 45157);
    assert_eq!(day_8(), 1337);
    assert_eq!(day_8b(), 1358);
    assert_eq!(day_9(), 36845998);
    assert_eq!(day_9b(), 4830226);
    assert_eq!(day_10(), 1876);
    assert_eq!(day_10b(), 14173478093824);
    assert_eq!(day_11(), 2204);
    assert_eq!(day_11b(), 1986);
    assert_eq!(day_12(), 998);
    assert_eq!(day_12b(), 71586);
    assert_eq!(day_13(), 3464);
    assert_eq!(day_13b(), 760171380521445);
    assert_eq!(day_14(), 14925946402938);
    assert_eq!(day_14b(), 3706820676200);
    assert_eq!(day_15(), 763);
    assert_eq!(day_15b(), 1876406);
    assert_eq!(day_16(), 20060);
    assert_eq!(day_16b(), 2843534243843);
    assert_eq!(day_17(), 353);
    assert_eq!(day_17b(), 2472);
    assert_eq!(day_18(), 3647606140187);
    assert_eq!(day_18b(), 323802071857594);
    assert_eq!(day_19(), 230);
    assert_eq!(day_19b(), 341);
    assert_eq!(day_20(), 18262194216271);
    assert_eq!(day_20b(), 2023);
    assert_eq!(day_21(), 2324);
    assert_eq!(day_21b(), "bxjvzk,hqgqj,sp,spl,hsksz,qzzzf,fmpgn,tpnnkc");
    assert_eq!(day_22(), 30780);
    assert_eq!(day_22b(), 36621);
    assert_eq!(day_23(), "98742365");
    assert_eq!(day_23b(), 294320513093);
    assert_eq!(day_24(), 434);
    assert_eq!(day_24b(), 3955);
    assert_eq!(day_25(), 7269858);
    assert_eq!(day_25b(), 1);
}

fn numbers_to_vec<T>(filename: &str) -> Vec<T>
where
    T: FromStr,
    T::Err: Debug,
{
    fs::read_to_string(filename)
        .expect("no file")
        .split_whitespace()
        .map(|s| {
            s.parse::<T>()
                .expect(format!("not a number {}", &s).as_str())
        })
        .collect()
}

fn lines_to_vec(filename: &str) -> Vec<String> {
    fs::read_to_string(filename)
        .expect("no file")
        .lines()
        .map(|s| s.to_owned())
        .collect()
}

fn day_0() -> i32 {
    println!("Hello World!");
    0
}

fn day_1() -> i32 {
    let v = numbers_to_vec::<i32>("data/day_1.txt");
    let mut set = HashSet::new();
    let target = 2020;
    for i in v {
        let f = target - i;
        if let Some(j) = set.get(&f) {
            return i * j;
        }
        set.insert(i);
    }
    0
}

fn day_1b() -> i64 {
    let v = numbers_to_vec::<i64>("data/day_1.txt");
    let target = 2020;
    for (i, v1) in v.iter().enumerate() {
        let target2 = target - v1;
        let mut set = HashSet::new();
        for &v2 in &v[i + 1..] {
            let f = target2 - v2;
            if let Some(v3) = set.get(&f) {
                return v1 * v2 * v3;
            }
            set.insert(v2);
        }
    }
    0
}

fn day_2() -> u32 {
    let v = lines_to_vec("data/day_2.txt");
    let re = Regex::new(r"^(\d+)+-(\d+)\s+([[:alpha:]]):\s+(\S+)$").unwrap();
    let mut correct = 0;

    for line in &v {
        if let Some(c) = re.captures(line) {
            let min = c.get(1).unwrap().as_str().parse::<usize>().unwrap();
            let max = c.get(2).unwrap().as_str().parse::<usize>().unwrap();
            let letter = c.get(3).unwrap().as_str().chars().next().unwrap();
            let password = c.get(4).unwrap().as_str();
            let count = password.chars().filter(|&c| c == letter).count();
            if count >= min && count <= max {
                correct += 1
            };
        }
    }

    correct
}

fn day_2b() -> u32 {
    let v = lines_to_vec("data/day_2.txt");
    let re = Regex::new(r"^(\d+)+-(\d+)\s+([[:alpha:]]):\s+(\S+)$").unwrap();
    let mut correct = 0;

    for line in &v {
        if let Some(c) = re.captures(line) {
            let min = c.get(1).unwrap().as_str().parse::<usize>().unwrap();
            let max = c.get(2).unwrap().as_str().parse::<usize>().unwrap();
            let letter = c.get(3).unwrap().as_str();
            let password = c.get(4).unwrap().as_str();
            let mut count = 0;
            if password.len() >= min && &password[min - 1..min] == letter {
                count += 1;
            }
            if password.len() >= max && &password[max - 1..max] == letter {
                count += 1;
            }
            if count == 1 {
                correct += 1
            }
        }
    }

    correct
}

fn day_3() -> u64 {
    let lines = lines_to_vec("data/day_3.txt");
    let lines = lines.iter().map(|r| r.as_bytes()).collect::<Vec<_>>();
    let right = 3;
    let down = 1;

    let rows = lines.len();
    let cols = lines[0].len();
    let mut x = 0;
    let mut y = 0;
    let mut trees = 0;

    while y < rows {
        if lines[y][x] == b'#' {
            trees += 1;
        }
        x = (x + right) % cols;
        y += down;
    }

    trees
}

fn day_3b() -> u64 {
    let lines = lines_to_vec("data/day_3.txt");
    let lines = lines.iter().map(|r| r.as_bytes()).collect::<Vec<_>>();
    let v = vec![(1, 1), (3, 1), (5, 1), (7, 1), (1, 2)];

    fn pom(lines: &Vec<&[u8]>, right: usize, down: usize) -> u64 {
        let rows = lines.len();
        let cols = lines[0].len();
        let mut x = 0;
        let mut y = 0;
        let mut trees = 0;

        while y < rows {
            if lines[y][x] == b'#' {
                trees += 1;
            }
            x = (x + right) % cols;
            y += down;
        }

        trees
    }

    v.iter().map(|p| pom(&lines, p.0, p.1)).product()
}

fn day_4() -> i32 {
    let mut h: HashMap<_, _> = vec![
        ("byr", 1),
        ("iyr", 1),
        ("eyr", 1),
        ("hgt", 1),
        ("hcl", 1),
        ("ecl", 1),
        ("pid", 1),
    ]
    .into_iter()
    .collect();

    let mut correct = 0;
    let lines = lines_to_vec("data/day_4.txt");

    for l in lines.iter() {
        if l.is_empty() {
            let mut all = true;
            for (_, v) in &mut h {
                if *v != 0 {
                    all = false;
                }
                *v = 1;
            }
            if all {
                correct += 1;
            }
            continue;
        }
        for pair in l.split_whitespace() {
            let first = pair.split(':').collect::<Vec<_>>()[0];
            if let Some(v) = h.get_mut(first) {
                if *v == 1 {
                    *v = 0;
                }
            }
        }
    }

    correct
}

fn day_4b() -> i32 {
    let validate_year = |s: &str, min: i32, max: i32| -> bool {
        match s.parse::<i32>() {
            Ok(n) => min <= n && n <= max,
            Err(_) => false,
        }
    };

    let re_height = Regex::new(r"^(\d+)(cm|in)$").unwrap();
    let validate_height = |s: &str| -> bool {
        if let Some(c) = re_height.captures(s) {
            let n = c.get(1).unwrap().as_str().parse::<i32>().unwrap();
            let f = c.get(2).unwrap().as_str();
            match f {
                "cm" => 150 <= n && n <= 193,
                "in" => 59 <= n && n <= 76,
                _ => false,
            }
        } else {
            false
        }
    };

    let re_hair_color = Regex::new(r"^#[0-9a-f]{6}$").unwrap();
    let validate_hair_color = |s: &str| -> bool { re_hair_color.is_match(s) };

    let re_eye_color = Regex::new(r"^(amb|blu|brn|gry|grn|hzl|oth)$").unwrap();
    let validate_eye_color = |s: &str| -> bool { re_eye_color.is_match(s) };

    let re_passport_id = Regex::new(r"^\d{9}$").unwrap();
    let validate_passport_id = |s: &str| -> bool { re_passport_id.is_match(s) };

    let mut correct = 0;
    let mut passed = 0;
    let lines = lines_to_vec("data/day_4.txt");

    for l in lines.iter() {
        if l.is_empty() {
            if passed == 7 {
                correct += 1;
            }
            passed = 0;
            continue;
        }
        for pair in l.split_whitespace() {
            let pair = pair.split(':').collect::<Vec<_>>();
            let first = pair[0];
            let second = pair[1];
            let valid = match first {
                "byr" => validate_year(second, 1920, 2002),
                "iyr" => validate_year(second, 2010, 2020),
                "eyr" => validate_year(second, 2020, 2030),
                "hgt" => validate_height(second),
                "hcl" => validate_hair_color(second),
                "ecl" => validate_eye_color(second),
                "pid" => validate_passport_id(second),
                _ => false,
            };
            if valid {
                passed += 1;
            }
        }
    }

    correct
}

fn day_5() -> i32 {
    let v = lines_to_vec("data/day_5.txt");
    let all_seats = 128 * 8;
    let mut seats = vec![false; all_seats];

    fn binary_find(arr: &str, lower: char) -> i32 {
        let mut start = 1;
        let mut end = usize::pow(2, arr.len() as u32);
        for c in arr.chars() {
            let m = start + (end - start + 1) / 2;
            if c == lower {
                end = m - 1;
            } else {
                start = m;
            }
        }
        (start - 1).try_into().unwrap()
    }

    let mut max = 0;
    for item in &v {
        let row = binary_find(&item[..7], 'F');
        let col = binary_find(&item[7..], 'L');
        let id = row * 8 + col;
        seats[(row * 8 + col) as usize] = true;
        if id > max {
            max = id;
        }
    }

    max
}

fn day_5b() -> i32 {
    let v = lines_to_vec("data/day_5.txt");
    let all_seats = 128 * 8;
    let mut seats = vec![false; all_seats];

    fn binary_find(arr: &str, lower: char) -> i32 {
        let mut start = 1;
        let mut end = usize::pow(2, arr.len() as u32);
        for c in arr.chars() {
            let m = start + (end - start + 1) / 2;
            if c == lower {
                end = m - 1;
            } else {
                start = m;
            }
        }
        (start - 1).try_into().unwrap()
    }

    let mut max = 0;
    for item in &v {
        let row = binary_find(&item[..7], 'F');
        let col = binary_find(&item[7..], 'L');
        let id = row * 8 + col;
        seats[(row * 8 + col) as usize] = true;
        if id > max {
            max = id;
        }
    }

    let mut my_id = 0;
    for i in 1..(all_seats - 2) {
        if seats[i - 1] && !seats[i] && seats[i + 1] {
            my_id = i;
        }
    }

    my_id as i32
}

fn day_6() -> i32 {
    let v = lines_to_vec("data/day_6.txt");
    let mut result: i32 = 0;
    let mut h: HashSet<char> = HashSet::new();
    for line in &v {
        if line.is_empty() {
            result += h.len() as i32;
            h.clear();
            continue;
        }
        for c in line.chars() {
            h.insert(c);
        }
    }
    result
}

fn day_6b() -> i32 {
    let v = lines_to_vec("data/day_6.txt");
    let mut result: i32 = 0;
    let mut h: Option<HashSet<char>> = None;
    for line in &v {
        if line.is_empty() {
            if let Some(h2) = h {
                result += h2.len() as i32;
                h = None;
            }
            continue;
        }
        let l: HashSet<char> = HashSet::from_iter(line.chars());
        if let Some(h2) = h {
            h = Some(HashSet::from_iter(h2.intersection(&l).cloned()));
        } else {
            h = Some(l);
        }
    }
    result
}

fn day_7() -> i32 {
    let lines = lines_to_vec("data/day_7.txt");
    let root_name = String::from("shiny gold");

    let mut connections: HashMap<String, Vec<String>> = HashMap::new();

    for line in &lines {
        let arr: Vec<&str> = line.split(" bags contain ").collect();
        let parent = arr[0];
        let values: Vec<&str> = arr[1].split(", ").collect();
        for val in values {
            if val.starts_with("no other bags") {
                continue;
            }
            let parts: Vec<&str> = val.split_whitespace().collect();
            let child = format!("{} {}", parts[1], parts[2]);
            let child_list = connections.entry(child).or_insert(vec![]);
            if !child_list.iter().any(|s| s == parent) {
                child_list.push(parent.to_owned());
            }
        }
    }

    let mut queue: VecDeque<&str> = VecDeque::new();
    let mut visited: HashSet<&str> = HashSet::new();

    visited.insert(&root_name);
    if let Some(list) = connections.get(&root_name) {
        for n in list {
            queue.push_back(n);
        }
    }

    let mut result = 0;
    while let Some(cur) = queue.pop_front() {
        if visited.contains(cur) {
            continue;
        };
        result += 1;

        visited.insert(cur);
        if let Some(list) = connections.get(cur) {
            for n in list {
                queue.push_back(n);
            }
        }
    }

    result
}

fn day_7b() -> u32 {
    let lines = lines_to_vec("data/day_7.txt");
    let root_name = String::from("shiny gold");
    let mut connections: HashMap<String, Vec<(String, u32)>> = HashMap::new();

    for line in &lines {
        let arr: Vec<&str> = line.split(" bags contain ").collect();
        let parent = arr[0];
        let parent_list = connections.entry(parent.to_owned()).or_insert(vec![]);
        let values: Vec<&str> = arr[1].split(", ").collect();
        for val in values {
            if val.starts_with("no other bags") {
                continue;
            }
            let parts: Vec<&str> = val.split_whitespace().collect();
            let count: u32 = parts[0].parse().unwrap();
            let child = format!("{} {}", parts[1], parts[2]);
            parent_list.push((child, count));
        }
    }

    fn visit(name: String, connections: &HashMap<String, Vec<(String, u32)>>) -> u32 {
        if let Some(children) = connections.get(name.as_str()) {
            let mut result = 0;
            for (child, count) in children {
                result += count + count * visit(child.clone(), connections);
            }
            result
        } else {
            0
        }
    }

    visit(root_name, &connections)
}

fn day_8() -> i32 {
    let lines = lines_to_vec("data/day_8.txt");

    #[derive(Debug)]
    enum Instruction {
        Nop,
        Jmp(i32),
        Acc(i32),
    }

    let instructions: Vec<Instruction> = lines
        .into_iter()
        .map(|line| {
            let arr: Vec<&str> = line.split_whitespace().collect();
            let val: i32 = arr[1].parse().unwrap();
            let instr = match arr[0] {
                "nop" => Instruction::Nop,
                "jmp" => Instruction::Jmp(val),
                "acc" => Instruction::Acc(val),
                _ => panic!("unknown instruction"),
            };
            instr
        })
        .collect();

    let mut arr: Vec<bool> = vec![false; instructions.len()];
    let mut acc = 0;
    let mut cur: usize = 0;
    while !arr[cur] {
        arr[cur] = true;
        match instructions[cur] {
            Instruction::Nop => cur += 1,
            Instruction::Jmp(val) => {
                cur = (cur as i32 + val) as usize;
            }
            Instruction::Acc(val) => {
                acc += val;
                cur += 1;
            }
        }
    }

    acc
}

fn day_8b() -> i32 {
    let lines = lines_to_vec("data/day_8.txt");

    #[derive(Copy, Clone, Debug)]
    enum Instruction {
        Nop(i32),
        Jmp(i32),
        Acc(i32),
    }

    impl Instruction {
        fn invert(&self) -> Option<Self> {
            match self {
                Self::Nop(val) => Some(Self::Jmp(*val)),
                Self::Jmp(val) => Some(Self::Nop(*val)),
                Self::Acc(_) => None,
            }
        }
    }

    let mut instructions: Vec<Instruction> = lines
        .into_iter()
        .map(|line| {
            let arr: Vec<&str> = line.split_whitespace().collect();
            let val: i32 = arr[1].parse().unwrap();
            let instr = match arr[0] {
                "nop" => Instruction::Nop(val),
                "jmp" => Instruction::Jmp(val),
                "acc" => Instruction::Acc(val),
                _ => panic!("unknown instruction"),
            };
            instr
        })
        .collect();

    fn execute(instructions: &Vec<Instruction>) -> Result<i32, i32> {
        let mut arr: Vec<bool> = vec![false; instructions.len()];
        let mut acc = 0;
        let mut cur: usize = 0;
        while !arr[cur] {
            arr[cur] = true;
            match instructions[cur] {
                Instruction::Nop(_) => cur += 1,
                Instruction::Jmp(val) => {
                    cur = (cur as i32 + val) as usize;
                }
                Instruction::Acc(val) => {
                    acc += val;
                    cur += 1;
                }
            }
            if cur == instructions.len() {
                return Ok(acc);
            }
        }
        Err(acc)
    }

    let mut cur = 0;
    while cur < instructions.len() {
        if let Some(inv) = instructions[cur].invert() {
            instructions[cur] = inv;
            if let Ok(res) = execute(&instructions) {
                return res;
            }
            instructions[cur] = inv.invert().unwrap();
        }
        cur += 1;
    }

    panic!("result not found");
}

fn day_9() -> i64 {
    let lines = numbers_to_vec::<i64>("data/day_9.txt");
    const PAST_RANGE: usize = 25;

    fn find_incorrect(lines: &Vec<i64>, past_range: usize) -> i64 {
        let mut hash: HashMap<i64, i32> = HashMap::new();
        for i in 0..past_range {
            *hash.entry(lines[i]).or_insert(0) += 1;
        }
        let mut l = 0;
        let mut r = past_range;
        while r < lines.len() {
            let sum = lines[r];

            let mut found = false;
            for i in l..r {
                let cur = lines[i];
                let to_find = sum - cur;
                if cur == to_find {
                    continue;
                }
                if *hash.get(&to_find).unwrap_or(&0) > 0 {
                    found = true;
                    break;
                }
            }
            if !found {
                return sum;
            }
            *hash.entry(lines[l]).or_insert(0) -= 1;
            l += 1;
            *hash.entry(lines[r]).or_insert(0) += 1;
            r += 1;
        }
        0
    }

    find_incorrect(&lines, PAST_RANGE)
}

fn day_9b() -> i64 {
    let lines = numbers_to_vec::<i64>("data/day_9.txt");
    const PAST_RANGE: usize = 25;

    fn find_incorrect(lines: &Vec<i64>, past_range: usize) -> i64 {
        let mut hash: HashMap<i64, i32> = HashMap::new();
        for i in 0..past_range {
            *hash.entry(lines[i]).or_insert(0) += 1;
        }
        let mut l = 0;
        let mut r = past_range;
        while r < lines.len() {
            let sum = lines[r];

            let mut found = false;
            for i in l..r {
                let cur = lines[i];
                let to_find = sum - cur;
                if cur == to_find {
                    continue;
                }
                if *hash.get(&to_find).unwrap_or(&0) > 0 {
                    found = true;
                    break;
                }
            }
            if !found {
                return sum;
            }
            *hash.entry(lines[l]).or_insert(0) -= 1;
            l += 1;
            *hash.entry(lines[r]).or_insert(0) += 1;
            r += 1;
        }
        0
    }

    fn find_sum(lines: &Vec<i64>, target: i64) -> Range<usize> {
        for i in 0..(lines.len() - 1) {
            let mut sum = lines[i];
            for j in (i + 1)..lines.len() {
                sum += lines[j];
                if sum == target {
                    return i..j + 1;
                }
                if sum > target {
                    break;
                }
            }
        }
        0..0
    }

    let incorrect = find_incorrect(&lines, PAST_RANGE);
    let range = find_sum(&lines, incorrect);
    let min = lines[range.clone()].iter().min().unwrap();
    let max = lines[range.clone()].iter().max().unwrap();

    min + max
}

fn day_10() -> u64 {
    let mut arr: Vec<i64> = numbers_to_vec("data/day_10.txt");

    arr.push(0);
    arr.sort();
    arr.push(arr.last().unwrap() + 3);
    let mut d1 = 0;
    let mut d3 = 0;
    for i in 1..(arr.len()) {
        match arr[i] - arr[i - 1] {
            1 => d1 += 1,
            2 => (),
            3 => d3 += 1,
            _ => panic!("wrong dist"),
        }
    }

    d1 * d3
}

fn day_10b() -> u64 {
    let mut arr: Vec<i64> = numbers_to_vec("data/day_10.txt");

    arr.push(0);
    arr.sort();
    arr.push(arr.last().unwrap() + 3);

    type Memo = HashMap<usize, u64>;
    let mut memo: Memo = HashMap::new();

    fn recursive(pos: usize, arr: &Vec<i64>, memo: &mut Memo) -> u64 {
        if pos + 1 >= arr.len() {
            return 1;
        }
        if memo.contains_key(&pos) {
            return memo[&pos];
        }
        let mut res = recursive(pos + 1, arr, memo);
        if pos + 2 >= arr.len() {
            memo.insert(pos, res);
            return res;
        }
        if arr[pos] + 3 >= arr[pos + 2] {
            res += recursive(pos + 2, arr, memo);
        }
        if pos + 3 >= arr.len() {
            memo.insert(pos, res);
            return res;
        }
        if arr[pos] + 3 >= arr[pos + 3] {
            res += recursive(pos + 3, arr, memo);
        }
        memo.insert(pos, res);
        res
    }

    recursive(0, &arr, &mut memo)
}

fn day_11() -> usize {
    let lines = lines_to_vec("data/day_11.txt");

    let w: isize = lines[0].len() as isize;
    let h: isize = lines.len() as isize;

    let cords: Vec<(isize, isize)> = vec![
        (-1, -1),
        (0, -1),
        (1, -1),
        (-1, 0),
        (1, 0),
        (-1, 1),
        (0, 1),
        (1, 1),
    ];

    let arr = lines.join("");
    let mut a: Vec<_> = arr.chars().collect();
    let mut b = a.clone();

    let occupied = |x: isize, y: isize, arr: &mut Vec<char>| -> u32 {
        let mut count = 0;
        for cord in &cords {
            let xx = x + cord.0;
            let yy = y + cord.1;
            if xx >= 0 && xx < w && yy >= 0 && yy < h {
                if arr[(yy * w + xx) as usize] == '#' {
                    count += 1;
                }
            }
        }
        count
    };

    let mut count = 0;
    loop {
        let mut cur = &mut a;
        let mut dup = &mut b;
        if count % 2 == 1 {
            cur = &mut b;
            dup = &mut a;
        }
        count += 1;

        let mut changed = 0;
        for y in 0..h {
            for x in 0..w {
                let i = (y * w + x) as usize;
                let n = match cur[i] {
                    '#' => {
                        let occ = occupied(x, y, cur);
                        if occ >= 4 {
                            'L'
                        } else {
                            '#'
                        }
                    }
                    'L' => {
                        let occ = occupied(x, y, cur);
                        if occ == 0 {
                            '#'
                        } else {
                            'L'
                        }
                    }
                    c => c,
                };
                if cur[i] != n {
                    changed += 1;
                }
                dup[i] = n;
            }
        }
        if changed == 0 {
            let left: usize = cur.iter().filter(|&&c| c == '#').count();
            break left;
        }
    }
}

fn day_11b() -> usize {
    let lines = lines_to_vec("data/day_11.txt");

    let w: isize = lines[0].len() as isize;
    let h: isize = lines.len() as isize;

    let cords: Vec<(isize, isize)> = vec![
        (-1, -1),
        (0, -1),
        (1, -1),
        (-1, 0),
        (1, 0),
        (-1, 1),
        (0, 1),
        (1, 1),
    ];

    let arr = lines.join("");
    let mut a: Vec<_> = arr.chars().collect();
    let mut b = a.clone();

    let within_board = |x: isize, y: isize| -> bool { x >= 0 && x < w && y >= 0 && y < h };

    let occupied = |px: isize, py: isize, arr: &mut Vec<char>, max_dist: i32| -> u32 {
        let mut count = 0;
        for cord in &cords {
            let mut x = px;
            let mut y = py;
            let mut dist = 0;
            let res = loop {
                x = x + cord.0;
                y = y + cord.1;
                if !within_board(x, y) {
                    break false;
                }
                match arr[(y * w + x) as usize] {
                    'L' => break false,
                    '#' => break true,
                    _ => (),
                }
                dist += 1;
                if dist == max_dist {
                    break false;
                }
            };
            if res {
                count += 1;
            }
        }
        count
    };

    let tolerance = 5;
    let max_dist = 0;

    let mut count = 0;
    loop {
        let mut cur = &mut a;
        let mut dup = &mut b;
        if count % 2 == 1 {
            cur = &mut b;
            dup = &mut a;
        }
        count += 1;

        let mut changed = 0;
        for y in 0..h {
            for x in 0..w {
                let i = (y * w + x) as usize;
                let n = match cur[i] {
                    '#' => {
                        let occ = occupied(x, y, cur, max_dist);
                        if occ >= tolerance {
                            'L'
                        } else {
                            '#'
                        }
                    }
                    'L' => {
                        let occ = occupied(x, y, cur, max_dist);
                        if occ == 0 {
                            '#'
                        } else {
                            'L'
                        }
                    }
                    c => c,
                };
                if cur[i] != n {
                    changed += 1;
                }
                dup[i] = n;
            }
        }
        if changed == 0 {
            let left: usize = cur.iter().filter(|&&c| c == '#').count();
            break left;
        }
    }
}

fn day_12() -> i32 {
    let lines = lines_to_vec("data/day_12.txt");

    let mut list: Vec<(char, i32)> = vec![];
    let regex = Regex::new(r"^([A-Z])(\d+)$").unwrap();
    for line in &lines {
        if let Some(c) = regex.captures(line) {
            let action = c.get(1).unwrap().as_str();
            let val = c.get(2).unwrap().as_str();
            list.push((action.chars().next().unwrap(), val.parse().unwrap()))
        }
    }

    let cycle = vec!['N', 'E', 'S', 'W'];
    let mut direction = 1;
    let mut x = 0;
    let mut y = 0;
    for ins in &list {
        match ins.0 {
            'N' => {
                y += ins.1;
            }
            'S' => {
                y -= ins.1;
            }
            'E' => {
                x += ins.1;
            }
            'W' => {
                x -= ins.1;
            }
            'L' => {
                let steps = ins.1 / 90;
                direction = (direction + 4 - steps) % 4;
            }
            'R' => {
                let steps = ins.1 / 90;
                direction = (direction + steps) % 4;
            }
            'F' => match cycle[direction as usize] {
                'N' => {
                    y += ins.1;
                }
                'S' => {
                    y -= ins.1;
                }
                'E' => {
                    x += ins.1;
                }
                'W' => {
                    x -= ins.1;
                }
                d => panic!("wrong direction: {}", d),
            },
            _ => {}
        }
    }

    x.abs() + y.abs()
}

fn day_12b() -> i32 {
    let lines = lines_to_vec("data/day_12.txt");

    let mut list: Vec<(char, i32)> = vec![];
    let regex = Regex::new(r"^([A-Z])(\d+)$").unwrap();
    for line in &lines {
        if let Some(c) = regex.captures(line) {
            let action = c.get(1).unwrap().as_str();
            let val = c.get(2).unwrap().as_str();
            list.push((action.chars().next().unwrap(), val.parse().unwrap()))
        }
    }

    let mut wx = 10;
    let mut wy = 1;
    let mut x = 0;
    let mut y = 0;
    for ins in &list {
        match ins.0 {
            'N' => {
                wy += ins.1;
            }
            'S' => {
                wy -= ins.1;
            }
            'E' => {
                wx += ins.1;
            }
            'W' => {
                wx -= ins.1;
            }
            'R' | 'L' => {
                let mut steps = ins.1 / 90;
                if ins.0 == 'L' {
                    steps = 4 - steps;
                }
                match steps {
                    1 => {
                        let (xa, ya) = (wy, -wx);
                        wx = xa;
                        wy = ya;
                    }
                    2 => {
                        let (xa, ya) = (-wx, -wy);
                        wx = xa;
                        wy = ya;
                    }
                    3 => {
                        let (xa, ya) = (-wy, wx);
                        wx = xa;
                        wy = ya;
                    }
                    _ => panic!("wrong turn"),
                }
            }
            'F' => {
                x += wx * ins.1;
                y += wy * ins.1;
            }
            _ => {}
        }
    }

    x.abs() + y.abs()
}

fn day_13() -> i32 {
    let lines = lines_to_vec("data/day_13.txt");

    let main_ts: i32 = lines[0].trim().parse().unwrap();
    let ts_list: Vec<_> = lines[1].split(',').collect();
    let ts_list: Vec<_> = ts_list.iter().filter(|&&s| s != "x").collect();
    let ts_list: Vec<i32> = ts_list.iter().map(|s| s.trim().parse().unwrap()).collect();
    let res = ts_list
        .iter()
        .map(|&i| (i, i - (main_ts % i)))
        .min_by(|a, b| a.1.cmp(&b.1))
        .unwrap();

    res.0 * res.1
}

fn day_13b() -> i64 {
    let lines = lines_to_vec("data/day_13.txt");

    let ts_list: Vec<_> = lines[1].split(',').collect();
    let ts_list: Vec<_> = ts_list
        .iter()
        .enumerate()
        .filter(|(_, &s)| s != "x")
        .map(|(i, s)| (i as i64, s.parse::<i64>().unwrap()))
        .collect();

    let mut step: i64 = ts_list.first().unwrap().1;
    let mut ts = step;
    let mut pos = 1;

    let check = |ts, pair: (i64, i64)| ((ts + pair.0) % pair.1) == 0;

    loop {
        if check(ts, ts_list[pos]) {
            step *= ts_list[pos].1;
            pos += 1;
            if pos == ts_list.len() {
                return ts;
            }
        }
        ts += step;
    }
}

fn day_14() -> u64 {
    let lines = lines_to_vec("data/day_14.txt");

    let mut mem = HashMap::new();
    let mut mask_and: u64 = 0;
    let mut mask_or: u64 = 0;

    for l in &lines {
        let pair = l.split_once(" = ").unwrap();
        if pair.0 == "mask" {
            let mask = pair.1.bytes();
            mask_and = u64::MAX;
            mask_or = 0;
            let mut bit: u64 = 1;
            for c in mask.rev() {
                match c {
                    b'X' => (),
                    b'0' => mask_and ^= bit,
                    b'1' => mask_or |= bit,
                    x => panic!("Wrong byte: '{}'", x),
                }
                bit <<= 1;
            }
        } else {
            let addr = pair.0[4..pair.0.len() - 1].parse::<u64>().unwrap();
            let val = pair.1.parse::<u64>().unwrap();
            let val = (val & mask_and) | mask_or;
            mem.insert(addr, val);
        }
    }

    let mut res: u64 = 0;
    for (_, v) in &mem {
        res += *v;
    }

    res
}

fn day_14b() -> u64 {
    let lines = lines_to_vec("data/day_14.txt");

    let mut mem = HashMap::new();
    let mut mask_or: u64 = 0;
    let mut fl = vec![];

    for l in &lines {
        let pair = l.split_once(" = ").unwrap();
        if pair.0 == "mask" {
            let mask = pair.1.bytes();
            fl = vec![];
            mask_or = 0;
            let mut bit: u64 = 1;
            for (i, c) in mask.rev().enumerate() {
                match c {
                    b'X' => fl.push(i as u64),
                    b'1' => mask_or |= bit,
                    b'0' => (),
                    x => panic!("Wrong byte: '{}'", x),
                }
                bit <<= 1;
            }
        } else {
            let val = pair.1.parse::<u64>().unwrap();
            let addr = pair.0[4..pair.0.len() - 1].parse::<u64>().unwrap();
            let addr = addr | mask_or;

            for i in 0..2_u64.pow(fl.len() as u32) {
                let mut perm = addr;
                let mut bit: u64 = 1;
                for j in &fl {
                    let mut cur = 1 << j;
                    if i & bit != 0 {
                        perm |= cur;
                    } else {
                        cur = !cur;
                        perm &= cur;
                    }
                    bit <<= 1;
                }
                mem.insert(perm, val);
            }
        }
    }

    let mut res: u64 = 0;
    for (_, v) in &mem {
        res += *v;
    }

    res
}

fn day_15() -> u64 {
    let start = vec![0, 14, 1, 3, 7, 9];

    let mut mem = HashMap::new();
    let mut pos = 1;
    for val in &start[0..start.len() - 1] {
        mem.insert(*val, pos);
        pos += 1;
    }
    let mut last = start[start.len() - 1];

    for _ in pos + 1..=2020 {
        let n = if mem.contains_key(&last) {
            pos - mem[&last]
        } else {
            0
        };
        mem.insert(last, pos);
        last = n;
        pos += 1;
    }

    last
}

fn day_15b() -> u64 {
    let start = vec![0, 14, 1, 3, 7, 9];

    let mut mem = HashMap::new();
    let mut pos = 1;
    for val in &start[0..start.len() - 1] {
        mem.insert(*val, pos);
        pos += 1;
    }
    let mut last = start[start.len() - 1];

    for _ in pos + 1..=30000000 {
        let n = if mem.contains_key(&last) {
            pos - mem[&last]
        } else {
            0
        };
        mem.insert(last, pos);

        last = n;
        pos += 1;
    }

    last
}

fn day_16() -> u32 {
    let lines = lines_to_vec("data/day_16.txt");

    let breaks: Vec<_> = lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.len() == 0)
        .map(|(i, _)| i)
        .collect();

    let rules = &lines[0..breaks[0]];
    let _ = &lines[breaks[0] + 2..breaks[1]];
    let other = &lines[breaks[1] + 2..lines.len()];

    let parse_range = |r: &str| {
        let (s, e) = r.split_once("-").unwrap();
        let s = s.parse::<u32>().unwrap();
        let e = e.parse::<u32>().unwrap();
        s..=e
    };

    let mut ranges = vec![];
    for rule in rules {
        let (_, r) = rule.split_once(": ").unwrap();
        let (r1, r2) = r.split_once(" or ").unwrap();
        ranges.push(parse_range(r1));
        ranges.push(parse_range(r2));
    }

    let mut sum = 0;
    for ticket in other {
        let nums = ticket.split(",");
        for num in nums {
            let num = num.parse::<u32>().unwrap();
            if !ranges.iter().any(|r| r.contains(&num)) {
                sum += num;
            }
        }
    }

    sum
}

fn day_16b() -> u64 {
    let lines = lines_to_vec("data/day_16.txt");

    let breaks: Vec<_> = lines
        .iter()
        .enumerate()
        .filter(|(_, l)| l.len() == 0)
        .map(|(i, _)| i)
        .collect();

    let rules = &lines[0..breaks[0]];
    let my_ticket = &lines[breaks[0] + 2..breaks[1]];
    let other = &lines[breaks[1] + 2..lines.len()];

    let parse_range = |r: &str| {
        let (s, e) = r.split_once("-").unwrap();
        let s = s.parse::<u32>().unwrap();
        let e = e.parse::<u32>().unwrap();
        s..=e
    };

    let mut rmap = HashMap::new();
    let mut ranges = vec![];
    for rule in rules {
        let (c, r) = rule.split_once(": ").unwrap();
        let (r1, r2) = r.split_once(" or ").unwrap();
        let r1 = parse_range(r1);
        let r2 = parse_range(r2);
        ranges.push(r1.clone());
        ranges.push(r2.clone());
        rmap.insert(c.to_owned(), vec![r1, r2]);
    }

    let my_ticket: Vec<u32> = my_ticket[0]
        .split(",")
        .collect::<Vec<_>>()
        .iter()
        .map(|num| num.parse::<u32>().unwrap())
        .collect();

    let other: Vec<Vec<u32>> = other
        .iter()
        .map(|ticket| {
            let arr = ticket.split(",").collect::<Vec<_>>();
            arr.iter().map(|num| num.parse::<u32>().unwrap()).collect()
        })
        .collect();

    let other: Vec<Vec<u32>> = other
        .into_iter()
        .filter(|nums| {
            nums.iter()
                .all(|num| ranges.iter().any(|r| r.contains(&num)))
        })
        .collect();

    let mut columns = vec![];
    for col in 0..other[0].len() {
        let mut common: HashSet<&str> = HashSet::new();
        let column: Vec<u32> = other.iter().map(|nums| nums[col]).collect();
        for (i, num) in column.iter().enumerate() {
            let mut klasses: HashSet<&str> = HashSet::new();
            for (klass, ranges) in &rmap {
                if ranges.iter().any(|r| r.contains(&num)) {
                    klasses.insert(klass.as_str());
                }
            }
            if i == 0 {
                common = klasses;
            } else {
                common = HashSet::from_iter(common.intersection(&klasses).cloned());
            }
        }
        columns.push(common);
    }

    let mut cmap = HashMap::new();
    loop {
        let first = columns.iter().enumerate().find(|(_, arr)| arr.len() == 1);
        if let Some((i, klass)) = first {
            let klass = klass.iter().next().unwrap().to_owned();
            for col in &mut columns {
                col.remove(klass);
            }
            cmap.insert(klass, i);
        } else {
            break;
        }
    }

    cmap.iter()
        .map(|(k, v)| {
            if k.starts_with("departure") {
                my_ticket[*v] as u64
            } else {
                1
            }
        })
        .product()
}

fn day_17() -> u32 {
    let lines = lines_to_vec("data/day_17.txt");

    let cycles = 6;
    let max_size: isize = lines.len() as isize + (cycles + 1) * 2;
    let start: isize = cycles + 1;
    let mut mem: Vec<[u8; 2]> = vec![[0, 0]; (max_size * max_size * max_size) as usize];

    let pos = |x: isize, y: isize, z: isize| -> usize {
        (z * max_size * max_size + y * max_size + x) as usize
    };

    for (y, line) in lines.iter().enumerate() {
        for (x, c) in line.chars().enumerate() {
            match c {
                '#' => mem[pos(start + x as isize, start + y as isize, start)][0] = 1,
                _ => {}
            }
        }
    }

    let offsets: [isize; 3] = [-1, 0, 1];
    let mut active = 0;

    for cycle in 0..cycles {
        let cur: usize = (cycle % 2) as usize;
        let next: usize = ((cycle + 1) % 2) as usize;
        active = 0;

        for z in 1..max_size - 2 {
            for y in 1..max_size - 2 {
                for x in 1..max_size - 2 {
                    let mut count = 0;
                    for dz in offsets {
                        for dy in offsets {
                            for dx in offsets {
                                if dz == 0 && dy == 0 && dx == 0 {
                                    continue;
                                }
                                if mem[pos(x + dx, y + dy, z + dz)][cur] == 1 {
                                    count += 1;
                                }
                            }
                        }
                    }

                    let p = pos(x, y, z);
                    if mem[p][cur] == 1 {
                        mem[p][next] = if count == 2 || count == 3 { 1 } else { 0 };
                    } else {
                        mem[p][next] = if count == 3 { 1 } else { 0 };
                    }
                    if mem[p][next] == 1 {
                        active += 1;
                    }
                }
            }
        }
    }

    active
}

fn day_17b() -> u32 {
    let lines = lines_to_vec("data/day_17.txt");

    let cycles = 6;
    let max_size: isize = lines.len() as isize + (cycles + 1) * 2;
    let start: isize = cycles + 1;
    let mut mem: Vec<[u8; 2]> = vec![[0, 0]; (max_size * max_size * max_size * max_size) as usize];

    let pos = |x: isize, y: isize, z: isize, w: isize| -> usize {
        (w * max_size * max_size * max_size + z * max_size * max_size + y * max_size + x) as usize
    };

    for (y, line) in lines.iter().enumerate() {
        for (x, c) in line.chars().enumerate() {
            match c {
                '#' => mem[pos(start + x as isize, start + y as isize, start, start)][0] = 1,
                _ => {}
            }
        }
    }

    let offsets: [isize; 3] = [-1, 0, 1];
    let mut active = 0;

    for cycle in 0..cycles {
        let cur: usize = (cycle % 2) as usize;
        let next: usize = ((cycle + 1) % 2) as usize;
        active = 0;

        for w in 1..max_size - 2 {
            for z in 1..max_size - 2 {
                for y in 1..max_size - 2 {
                    for x in 1..max_size - 2 {
                        let mut count = 0;
                        for dw in offsets {
                            for dz in offsets {
                                for dy in offsets {
                                    for dx in offsets {
                                        if dw == 0 && dz == 0 && dy == 0 && dx == 0 {
                                            continue;
                                        }
                                        if mem[pos(x + dx, y + dy, z + dz, w + dw)][cur] == 1 {
                                            count += 1;
                                        }
                                    }
                                }
                            }
                        }

                        let p = pos(x, y, z, w);
                        if mem[p][cur] == 1 {
                            mem[p][next] = if count == 2 || count == 3 { 1 } else { 0 };
                        } else {
                            mem[p][next] = if count == 3 { 1 } else { 0 };
                        }
                        if mem[p][next] == 1 {
                            active += 1;
                        }
                    }
                }
            }
        }
    }

    active
}

fn day_18() -> i64 {
    let lines = lines_to_vec("data/day_18.txt");

    #[derive(Clone, Copy)]
    enum Op {
        Plus,
        Multiply,
    }

    impl Op {
        fn exec(&self, acc: i64, n: i64) -> i64 {
            match self {
                Op::Plus => acc + n,
                Op::Multiply => acc * n,
            }
        }
    }

    let mut res = 0;
    for line in lines {
        let mut acc_stack = vec![];
        let mut op_stack = vec![];
        let mut op = Op::Plus;
        let mut acc = 0;

        for c in line.chars() {
            match c {
                d @ '0'..='9' => {
                    let n = d.to_digit(10).unwrap() as i64;
                    acc = op.exec(acc, n);
                }
                '+' => {
                    op = Op::Plus;
                }
                '*' => {
                    op = Op::Multiply;
                }
                '(' => {
                    acc_stack.push(acc);
                    op_stack.push(op);
                    acc = 0;
                    op = Op::Plus;
                }
                ')' => {
                    let n = acc;
                    acc = acc_stack.pop().unwrap();
                    op = op_stack.pop().unwrap();
                    acc = op.exec(acc, n);
                }
                _ => {}
            }
        }
        res += acc;
    }

    res
}

fn day_18b() -> i64 {
    let lines = lines_to_vec("data/day_18.txt");

    #[derive(Clone, Copy)]
    enum Op {
        Plus,
        Multiply,
    }
    impl Op {
        fn calc(&self, acc: i64, n: i64, st: &mut Vec<i64>) -> i64 {
            match self {
                Op::Plus => acc + n,
                Op::Multiply => {
                    st.push(acc);
                    n
                }
            }
        }
    }

    let mut res = 0;
    for line in lines {
        let mut mul_stack = vec![];
        let mut mul_mul_stack = vec![];
        let mut acc_stack = vec![];
        let mut op_stack = vec![];
        let mut op = Op::Plus;
        let mut acc = 0;

        for c in line.chars() {
            match c {
                d @ '0'..='9' => {
                    let n = d.to_digit(10).unwrap() as i64;
                    acc = op.calc(acc, n, &mut mul_stack);
                }
                '+' => {
                    op = Op::Plus;
                }
                '*' => {
                    op = Op::Multiply;
                }
                '(' => {
                    acc_stack.push(acc);
                    op_stack.push(op);
                    mul_mul_stack.push(mul_stack);

                    mul_stack = vec![];
                    op = Op::Plus;
                    acc = 0;
                }
                ')' => {
                    mul_stack.push(acc);
                    let n = mul_stack.iter().product();

                    acc = acc_stack.pop().unwrap();
                    op = op_stack.pop().unwrap();
                    mul_stack = mul_mul_stack.pop().unwrap();

                    acc = op.calc(acc, n, &mut mul_stack);
                }
                _ => {}
            }
        }
        mul_stack.push(acc);
        let line_sum = mul_stack.iter().product::<i64>();
        res += line_sum;
    }

    res
}

fn day_19() -> i32 {
    let lines = lines_to_vec("data/day_19.txt");

    #[derive(Debug)]
    enum Rule {
        None,
        Letter(char),
        Recursion(Vec<Vec<usize>>),
    }

    let regex = Regex::new(r"^(\d+): (.+)").unwrap();
    let mut to_check = vec![];
    let mut rules = vec![];
    for _ in 0..lines.len() {
        rules.push(Rule::None);
    }

    let parse_nums = |s: &str| -> Vec<usize> {
        s.split(" ")
            .map(|n| n.parse::<usize>().unwrap())
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
    };

    for line in &lines {
        if let Some(c) = regex.captures(line) {
            let num = c.get(1).unwrap().as_str().parse::<usize>().unwrap();
            let s = c.get(2).unwrap().as_str();
            if s.starts_with("\"") {
                rules[num] = Rule::Letter(s.chars().collect::<Vec<_>>()[1]);
            } else {
                if let Some((s1, s2)) = s.split_once(" | ") {
                    rules[num] = Rule::Recursion(vec![parse_nums(s1), parse_nums(s2)])
                } else {
                    rules[num] = Rule::Recursion(vec![parse_nums(s)]);
                }
            }
        } else if line.len() > 0 {
            to_check.push(line);
        }
    }

    fn check(chars: &[char], pos: usize, rules: &Vec<Rule>, stack: &mut Vec<usize>) -> bool {
        if pos == chars.len() && stack.len() == 0 {
            return true;
        }
        if pos == chars.len() || stack.len() == 0 {
            return false;
        }
        match &rules[*stack.last().unwrap()] {
            Rule::Letter(letter) => {
                return if *letter == chars[pos] {
                    let memo = stack.pop().unwrap();
                    let res = check(chars, pos + 1, rules, stack);
                    stack.push(memo);
                    res
                } else {
                    false
                }
            }
            Rule::Recursion(lists) => {
                for list in lists {
                    let memo = stack.pop().unwrap();
                    let added = list.len();
                    for n in list {
                        stack.push(*n);
                    }
                    let res = check(chars, pos, rules, stack);
                    stack.truncate(stack.len() - added);
                    stack.push(memo);
                    if res {
                        return true;
                    }
                }
                return false;
            }
            Rule::None => {
                panic!("Unexpected None rule");
            }
        }
    }

    let mut res = 0;
    let mut start = vec![0];
    for s in &to_check {
        let chars: Vec<_> = s.chars().collect();
        if check(&chars, 0, &rules, &mut start) {
            res += 1;
        }
    }

    res
}

fn day_19b() -> i32 {
    let lines = lines_to_vec("data/day_19.txt");

    #[derive(Debug)]
    enum Rule {
        None,
        Letter(char),
        Recursion(Vec<Vec<usize>>),
    }

    let regex = Regex::new(r"^(\d+): (.+)").unwrap();
    let mut to_check = vec![];
    let mut rules = vec![];
    for _ in 0..lines.len() {
        rules.push(Rule::None);
    }

    let parse_nums = |s: &str| -> Vec<usize> {
        s.split(" ")
            .map(|n| n.parse::<usize>().unwrap())
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
    };

    for line in &lines {
        if let Some(c) = regex.captures(line) {
            let num = c.get(1).unwrap().as_str().parse::<usize>().unwrap();
            let s = c.get(2).unwrap().as_str();
            if s.starts_with("\"") {
                rules[num] = Rule::Letter(s.chars().collect::<Vec<_>>()[1]);
            } else {
                if let Some((s1, s2)) = s.split_once(" | ") {
                    rules[num] = Rule::Recursion(vec![parse_nums(s1), parse_nums(s2)])
                } else {
                    rules[num] = Rule::Recursion(vec![parse_nums(s)]);
                }
            }
        } else if line.len() > 0 {
            to_check.push(line);
        }
    }

    rules[8] = Rule::Recursion(vec![parse_nums("42"), parse_nums("42 8")]);
    rules[11] = Rule::Recursion(vec![parse_nums("42 31"), parse_nums("42 11 31")]);

    fn check(chars: &[char], pos: usize, rules: &Vec<Rule>, stack: &mut Vec<usize>) -> bool {
        if pos == chars.len() && stack.len() == 0 {
            return true;
        }
        if pos == chars.len() || stack.len() == 0 {
            return false;
        }
        match &rules[*stack.last().unwrap()] {
            Rule::Letter(letter) => {
                return if *letter == chars[pos] {
                    let memo = stack.pop().unwrap();
                    let res = check(chars, pos + 1, rules, stack);
                    stack.push(memo);
                    res
                } else {
                    false
                }
            }
            Rule::Recursion(lists) => {
                if stack.len() > chars.len() / 2 {
                    return false;
                }
                for list in lists {
                    let memo = stack.pop().unwrap();
                    let added = list.len();
                    for n in list {
                        stack.push(*n);
                    }
                    let res = check(chars, pos, rules, stack);
                    stack.truncate(stack.len() - added);
                    stack.push(memo);
                    if res {
                        return true;
                    }
                }
                return false;
            }
            Rule::None => {
                panic!("Unexpected None rule");
            }
        }
    }

    let mut res = 0;
    let mut start = vec![0];
    for s in &to_check {
        let chars: Vec<_> = s.chars().collect();
        if check(&chars, 0, &rules, &mut start) {
            res += 1;
        }
    }

    res
}

fn day_20() -> i64 {
    let lines = lines_to_vec("data/day_20.txt");

    type Tile = Vec<[Vec<u16>; 2]>;
    type RB = HashMap<u16, u16>;
    type B2I = HashMap<u16, Vec<usize>>;
    type Sol = Vec<Vec<u16>>;
    type Free = Vec<bool>;

    let mut tile_def: Tile = vec![];
    let mut tile_uid: i64 = 0;
    let mut id_2_uid = vec![];
    let mut tile_rows = vec![];
    let mut rev_bits: RB = HashMap::new();
    let mut br_2_ids: B2I = HashMap::new();

    fn sum_bits<'a>(iter: impl DoubleEndedIterator<Item = &'a u16>) -> u16 {
        iter.rev()
            .enumerate()
            .map(|(i, bit)| bit * 2_u16.pow(i as u32))
            .sum()
    }

    fn top(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows[0].iter())
    }

    fn top_rev(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.first().unwrap().iter().rev())
    }

    fn right(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.iter().map(|r| &r[r.len() - 1]))
    }

    fn right_rev(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.iter().rev().map(|r| &r[r.len() - 1]))
    }

    fn bottom(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.last().unwrap().iter().rev())
    }

    fn bottom_rev(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.last().unwrap().iter())
    }

    fn left(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.iter().rev().map(|r| &r[0]))
    }

    fn left_rev(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.iter().map(|r| &r[0]))
    }

    for line in lines {
        if line.starts_with("Tile") {
            if let Some((_, num)) = line.split_once(" ") {
                tile_uid = (&num[0..num.len() - 1]).parse().unwrap();
            } else {
                panic!("Cannot parse tile id: {}", line);
            }
        } else if line.len() > 0 {
            let bits: Vec<u16> = line
                .chars()
                .map(|c| match c {
                    '#' => 1,
                    '.' => 0,
                    x => panic!("Unknown char: {}", x),
                })
                .collect();
            tile_rows.push(bits);
        } else {
            let tile_id = id_2_uid.len();
            id_2_uid.push(tile_uid);

            let t = top(&tile_rows);
            let r = right(&tile_rows);
            let b = bottom(&tile_rows);
            let l = left(&tile_rows);
            let a = vec![t, r, b, l];
            for border in &a {
                br_2_ids.entry(*border).or_insert(vec![]).push(tile_id);
            }
            let br = bottom_rev(&tile_rows);
            let rr = right_rev(&tile_rows);
            let tr = top_rev(&tile_rows);
            let lr = left_rev(&tile_rows);
            let ar = vec![br, rr, tr, lr];
            for border in &ar {
                br_2_ids.entry(*border).or_insert(vec![]).push(tile_id);
            }
            tile_def.push([a, ar]);
            rev_bits.insert(t, tr);
            rev_bits.insert(tr, t);
            rev_bits.insert(r, rr);
            rev_bits.insert(rr, r);
            rev_bits.insert(l, lr);
            rev_bits.insert(lr, l);
            rev_bits.insert(b, br);
            rev_bits.insert(br, b);
            tile_rows.truncate(0);
        }
    }

    let all = tile_def.len();
    let cols = (all as f64).sqrt() as usize;
    let mut solution: Sol = vec![];
    let mut free: Free = vec![true; all];

    fn check(
        tile_def: &Tile,
        br_2_ids: &B2I,
        rev_bits: &RB,
        cols: usize,
        solution: &mut Sol,
        free: &mut Free,
        id: usize,
    ) -> bool {
        let pos = solution.len();
        let row: usize = pos / cols;
        let col: usize = pos % cols;
        free[id] = false;
        for (d, def) in tile_def[id].iter().enumerate() {
            for offset in 0..4 {
                let mut fit = vec![];
                for i in 0..4 {
                    fit.push(def[(offset + i) % 4]);
                }
                if row > 0 && fit[0] != rev_bits[&solution[(row - 1) * cols + col][2]] {
                    continue;
                }
                if col > 0 && fit[3] != rev_bits[&solution[row * cols + col - 1][1]] {
                    continue;
                }
                fit.push(id as u16);
                fit.push(d as u16);
                let border: u16 = if col == cols - 1 {
                    solution[row * cols][2]
                } else {
                    fit[1]
                };

                solution.push(fit);
                if solution.len() == tile_def.len() {
                    return true;
                }
                for &pid in &br_2_ids[&border] {
                    if free[pid] {
                        if check(tile_def, br_2_ids, rev_bits, cols, solution, free, pid) {
                            return true;
                        }
                    }
                }
                solution.pop();
            }
        }
        free[id] = true;
        false
    }

    for id in 0..all {
        if check(
            &tile_def,
            &br_2_ids,
            &rev_bits,
            cols,
            &mut solution,
            &mut free,
            id,
        ) {
            let ids: Vec<_> = solution.iter().map(|v| v[4].clone()).collect();
            let corners = vec![ids[0], ids[cols - 1], ids[all - cols], ids[all - 1]];
            return corners.iter().map(|id| id_2_uid[*id as usize]).product();
        }
    }

    panic!("no solution")
}

fn day_20b() -> i64 {
    let lines = lines_to_vec("data/day_20.txt");

    type Tile = Vec<[Vec<u16>; 2]>;
    type RB = HashMap<u16, u16>;
    type B2I = HashMap<u16, Vec<usize>>;
    type Sol = Vec<Vec<u16>>;
    type Free = Vec<bool>;

    let mut tile_bits: Vec<Vec<Vec<u16>>> = vec![];
    let mut tile_def: Tile = vec![];
    let mut tile_uid: i64 = 0;
    let mut id_2_uid = vec![];
    let mut tile_rows = vec![];
    let mut rev_bits: RB = HashMap::new();
    let mut br_2_ids: B2I = HashMap::new();

    fn sum_bits<'a>(iter: impl DoubleEndedIterator<Item = &'a u16>) -> u16 {
        iter.rev()
            .enumerate()
            .map(|(i, bit)| bit * 2_u16.pow(i as u32))
            .sum()
    }

    fn top(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows[0].iter())
    }

    fn top_rev(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.first().unwrap().iter().rev())
    }

    fn right(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.iter().map(|r| &r[r.len() - 1]))
    }

    fn right_rev(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.iter().rev().map(|r| &r[r.len() - 1]))
    }

    fn bottom(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.last().unwrap().iter().rev())
    }

    fn bottom_rev(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.last().unwrap().iter())
    }

    fn left(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.iter().rev().map(|r| &r[0]))
    }

    fn left_rev(tile_rows: &Vec<Vec<u16>>) -> u16 {
        sum_bits(tile_rows.iter().map(|r| &r[0]))
    }

    for line in lines {
        if line.starts_with("Tile") {
            if let Some((_, num)) = line.split_once(" ") {
                tile_uid = (&num[0..num.len() - 1]).parse().unwrap();
            } else {
                panic!("Cannot parse tile id: {}", line);
            }
        } else if line.len() > 0 {
            let bits: Vec<u16> = line
                .chars()
                .map(|c| match c {
                    '#' => 1,
                    '.' => 0,
                    x => panic!("Unknown char: {}", x),
                })
                .collect();
            tile_rows.push(bits);
        } else {
            let tile_id = id_2_uid.len();
            id_2_uid.push(tile_uid);

            let t = top(&tile_rows);
            let r = right(&tile_rows);
            let b = bottom(&tile_rows);
            let l = left(&tile_rows);
            let a = vec![t, r, b, l];
            for border in &a {
                br_2_ids.entry(*border).or_insert(vec![]).push(tile_id);
            }
            let br = bottom_rev(&tile_rows);
            let rr = right_rev(&tile_rows);
            let tr = top_rev(&tile_rows);
            let lr = left_rev(&tile_rows);
            let ar = vec![br, rr, tr, lr];
            for border in &ar {
                br_2_ids.entry(*border).or_insert(vec![]).push(tile_id);
            }
            tile_def.push([a, ar]);
            rev_bits.insert(t, tr);
            rev_bits.insert(tr, t);
            rev_bits.insert(r, rr);
            rev_bits.insert(rr, r);
            rev_bits.insert(l, lr);
            rev_bits.insert(lr, l);
            rev_bits.insert(b, br);
            rev_bits.insert(br, b);

            let pom = std::mem::take(&mut tile_rows);
            tile_bits.push(pom);
        }
    }

    let all = tile_def.len();
    let cols = (all as f64).sqrt() as usize;
    let mut solution: Sol = vec![];
    let mut free: Free = vec![true; all];

    fn check(
        tile_def: &Tile,
        br_2_ids: &B2I,
        rev_bits: &RB,
        cols: usize,
        solution: &mut Sol,
        free: &mut Free,
        id: usize,
    ) -> bool {
        let pos = solution.len();
        let row: usize = pos / cols;
        let col: usize = pos % cols;
        free[id] = false;
        for (d, def) in tile_def[id].iter().enumerate() {
            for offset in 0..4 {
                let mut fit = vec![];
                for i in 0..4 {
                    fit.push(def[(offset + i) % 4]);
                }
                if row > 0 && fit[0] != rev_bits[&solution[(row - 1) * cols + col][2]] {
                    continue;
                }
                if col > 0 && fit[3] != rev_bits[&solution[row * cols + col - 1][1]] {
                    continue;
                }
                fit.push(id as u16);
                fit.push(d as u16);
                fit.push(offset as u16);
                let border: u16 = if col == cols - 1 {
                    solution[row * cols][2]
                } else {
                    fit[1]
                };

                solution.push(fit);
                if solution.len() == tile_def.len() {
                    return true;
                }
                for &pid in &br_2_ids[&border] {
                    if free[pid] {
                        if check(tile_def, br_2_ids, rev_bits, cols, solution, free, pid) {
                            return true;
                        }
                    }
                }
                solution.pop();
            }
        }
        free[id] = true;
        false
    }

    for id in 0..all {
        if check(
            &tile_def,
            &br_2_ids,
            &rev_bits,
            cols,
            &mut solution,
            &mut free,
            id,
        ) {
            break;
        }
    }

    fn flip(tile: &mut Vec<Vec<u16>>) {
        let mut i = 0;
        let mut j = tile.len() - 1;
        while i < j {
            tile.swap(i, j);
            i += 1;
            j -= 1;
        }
    }

    fn rotate(tile: &mut Vec<Vec<u16>>, times: u16) {
        let n = tile.len();
        let k = n / 2;
        for _ in 0..times % 4 {
            for j in 0..=k {
                for i in j..n - 1 - j {
                    let tl = tile[j][i];
                    let tr = tile[i][n - 1 - j];
                    let br = tile[n - 1 - j][n - 1 - i];
                    let bl = tile[n - 1 - i][j];
                    tile[j][i] = bl;
                    tile[i][n - 1 - j] = tl;
                    tile[n - 1 - j][n - 1 - i] = tr;
                    tile[n - 1 - i][j] = br;
                }
            }
        }
    }

    fn print_tile(tile: &Vec<Vec<u16>>) {
        for row in tile {
            let row: Vec<_> = row
                .iter()
                .map(|b| if *b == 1 { '#' } else { '.' })
                .collect();
            for c in row {
                print!("{}", c)
            }
            println!();
        }
    }

    let tile_size = tile_bits[0].len() - 2;
    let mut sea = vec![];
    for _ in 0..cols * tile_size {
        sea.push(vec![]);
    }

    for (pos, def) in solution.iter().enumerate() {
        let row: usize = pos / cols;
        let mut tile = tile_bits[def[4] as usize].clone();
        if def[5] == 1 {
            flip(&mut tile);
        }
        rotate(&mut tile, 4 - def[6]);
        for (r, tile_row) in tile.iter().enumerate() {
            if r == 0 || r == tile.len() - 1 {
                continue;
            }
            for i in 1..tile_row.len() - 1 {
                sea[row * tile_size + r - 1].push(tile_row[i]);
            }
        }
    }

    let dragon = r#"                  # 
#    ##    ##    ###
 #  #  #  #  #  #   "#;
    let dragon: Vec<_> = dragon.split('\n').collect();
    let dragon_height = dragon.len();
    let dragon_width = dragon[0].len();
    let mut coords = vec![];
    for (row, line) in dragon.iter().enumerate() {
        for (col, c) in line.chars().enumerate() {
            if c == '#' {
                coords.push((row, col));
            }
        }
    }

    for f in 0..=1 {
        let mut rsea = sea.clone();
        if f == 1 {
            flip(&mut rsea);
        }
        for ro in 0..=3 {
            rotate(&mut rsea, ro);
            let mut dragons = vec![];
            for row in 0..rsea.len() - dragon_height {
                for col in 0..rsea[0].len() - dragon_width {
                    let is_dragon = coords.iter().all(|(r, c)| rsea[row + r][col + c] == 1);
                    if is_dragon {
                        dragons.push((row, col));
                    }
                }
            }
            if dragons.len() > 0 {
                for (row, col) in &dragons {
                    for (r, c) in &coords {
                        rsea[row + r][col + c] = 0;
                    }
                }
                return rsea
                    .iter()
                    .map(|row| row.iter().map(|v| *v as i64).sum::<i64>())
                    .collect::<Vec<_>>()
                    .iter()
                    .sum::<i64>();
            }
        }
    }

    panic!("no solution")
}

fn day_21() -> i32 {
    let lines = lines_to_vec("data/day_21.txt");

    let mut foods = vec![];
    for line in &lines {
        if let Some((food, allergens)) = line.split_once(" (contains ") {
            let allergens = &allergens[0..allergens.len() - 1];
            let allergens: Vec<_> = allergens.split(", ").collect();
            let ingredients: Vec<_> = food.split(" ").collect();
            foods.push((ingredients, allergens));
        }
    }

    let mut h = HashMap::new();
    for (ingredients, allergens) in &foods {
        for allergen in allergens {
            let e = h.entry(allergen).or_insert(vec![]);
            e.push(ingredients);
        }
    }

    let mut h2 = HashMap::new();
    for (k, list) in &h {
        if list.len() == 1 {
            let i: HashSet<_> = list[0].iter().collect();
            h2.insert(k.clone(), i);
        } else {
            let mut intersection: HashSet<_> = list[0].iter().collect();
            for v in &list[1..] {
                let pom: HashSet<_> = v.iter().collect();
                intersection = intersection.intersection(&pom).cloned().collect();
            }
            h2.insert(k.clone(), intersection);
        }
    }

    let mut all = HashSet::new();
    for (_, v) in &h2 {
        for i in v {
            all.insert(i);
        }
    }

    let mut result = 0;
    for (ingredients, _) in &foods {
        for ingredient in ingredients {
            if !all.contains(&ingredient) {
                result += 1;
            }
        }
    }

    result
}

fn day_21b() -> String {
    let lines = lines_to_vec("data/day_21.txt");

    let mut foods = vec![];
    for line in &lines {
        if let Some((food, allergens)) = line.split_once(" (contains ") {
            let allergens = &allergens[0..allergens.len() - 1];
            let allergens: Vec<_> = allergens.split(", ").collect();
            let ingredients: Vec<_> = food.split(" ").collect();
            foods.push((ingredients, allergens));
        }
    }

    let mut h = HashMap::new();
    for (ingredients, allergens) in &foods {
        for allergen in allergens {
            let e = h.entry(allergen).or_insert(vec![]);
            e.push(ingredients);
        }
    }

    let mut h2 = HashMap::new();
    for (k, list) in &h {
        if list.len() == 1 {
            let i: HashSet<_> = list[0].iter().collect();
            h2.insert(k.clone(), i);
        } else {
            let mut intersection: HashSet<_> = list[0].iter().collect();
            for v in &list[1..] {
                let pom: HashSet<_> = v.iter().collect();
                intersection = intersection.intersection(&pom).cloned().collect();
            }
            h2.insert(k.clone(), intersection);
        }
    }

    let mut all = HashSet::new();
    let mut h3 = HashMap::new();
    while h2.len() > 0 {
        let hh = h2.clone();
        for (k, v) in &hh {
            if v.len() == 1 {
                let elem = v.iter().next().unwrap();
                h3.insert(k.clone(), elem.clone());
                h2.remove(k);
                all.insert(*elem);
            } else {
                let i: HashSet<_> = v.difference(&all).cloned().collect();
                h2.insert(k, i);
            }
        }
    }

    let mut sort: Vec<_> = h3.keys().collect();
    sort.sort();
    let sorted: Vec<_> = sort.iter().map(|s| h3[*s].to_owned()).collect();

    sorted.join(",")
}

fn day_22() -> i32 {
    let lines = lines_to_vec("data/day_22.txt");

    let mut stacks = vec![VecDeque::new(), VecDeque::new()];
    let mut cur_stack = &mut stacks[0];

    for l in &lines {
        if l.len() == 0 {
            continue;
        }
        if l.contains("1:") {
            cur_stack = &mut stacks[0];
            continue;
        }
        if l.contains("2:") {
            cur_stack = &mut stacks[1];
            continue;
        }
        let card: i32 = l.parse().unwrap();
        cur_stack.push_back(card);
    }

    loop {
        if stacks.iter().any(|v| v.len() == 0) {
            break;
        }
        let a = stacks[0].pop_front().unwrap();
        let b = stacks[1].pop_front().unwrap();
        if a > b {
            stacks[0].push_back(a);
            stacks[0].push_back(b);
        } else {
            stacks[1].push_back(b);
            stacks[1].push_back(a);
        }
    }

    let winner = if stacks[0].len() > 0 {
        &stacks[0]
    } else {
        &stacks[1]
    };

    let res = winner
        .iter()
        .rev()
        .enumerate()
        .map(|(i, c)| (i as i32 + 1) * c)
        .sum();

    res
}

fn day_22b() -> i32 {
    let lines = lines_to_vec("data/day_22.txt");

    let mut s1 = vec![];
    let mut s2 = vec![];
    let mut cur_stack = &mut s1;
    for l in &lines {
        if l.len() == 0 {
            continue;
        }
        if l.contains("1:") {
            cur_stack = &mut s1;
            continue;
        }
        if l.contains("2:") {
            cur_stack = &mut s2;
            continue;
        }
        let card: i32 = l.parse().unwrap();
        cur_stack.push(card);
    }

    fn deck_res<'a>(d: impl DoubleEndedIterator<Item = &'a i32>) -> i32 {
        d.rev().enumerate().map(|(i, c)| (i as i32 + 1) * c).sum()
    }

    fn deck_hash<'a>(d: impl Iterator<Item = &'a i32>) -> u64 {
        let mut h = DefaultHasher::new();
        for i in d {
            i.hash(&mut h);
        }
        h.finish()
    }

    fn play(p1: &[i32], p2: &[i32]) -> (bool, i32) {
        let mut s1: VecDeque<_> = p1.iter().copied().collect();
        let mut s2: VecDeque<_> = p2.iter().copied().collect();
        let mut h1: HashSet<u64> = HashSet::new();
        let mut h2: HashSet<u64> = HashSet::new();

        loop {
            if s1.len() == 0 || s2.len() == 0 {
                break;
            }
            let d = deck_hash(s1.iter());
            if h1.contains(&d) {
                return (true, 0);
            }
            h1.insert(d);
            let d = deck_hash(s2.iter());
            if h2.contains(&d) {
                return (true, 0);
            }
            h2.insert(d);

            let a = s1.pop_front().unwrap();
            let b = s2.pop_front().unwrap();

            if s1.len() as i32 >= a && s2.len() as i32 >= b {
                let a1 = s1.make_contiguous();
                let a2 = s2.make_contiguous();
                let rec = play(&a1[0..a as usize], &a2[0..b as usize]);
                if rec.0 {
                    s1.push_back(a);
                    s1.push_back(b);
                } else {
                    s2.push_back(b);
                    s2.push_back(a);
                }
            } else {
                if a > b {
                    s1.push_back(a);
                    s1.push_back(b);
                } else {
                    s2.push_back(b);
                    s2.push_back(a);
                }
            }
        }

        if s1.len() > 0 {
            (true, deck_res(s1.iter()))
        } else {
            (false, deck_res(s2.iter()))
        }
    }

    play(&s1, &s2).1
}

fn day_23() -> String {
    let input = "792845136";
    let rounds = 100;
    let take = 3;

    let mut circle: Vec<_> = input.chars().map(|c| c.to_digit(10).unwrap()).collect();
    let max = circle.len();

    for _ in 1..=rounds {
        let mut dest = circle[0] - 1;
        let pos = 'search: loop {
            for i in (1 + take)..max {
                if circle[i] == dest {
                    break 'search i;
                }
            }
            if dest == 0 {
                dest = 9;
            } else {
                dest -= 1;
            }
        };

        let mut new_circle = vec![];
        for i in (1 + take)..=pos {
            new_circle.push(circle[i]);
        }
        for i in 1..take + 1 {
            new_circle.push(circle[i]);
        }
        for i in pos + 1..max {
            new_circle.push(circle[i]);
        }
        new_circle.push(circle[0]);
        circle = new_circle;
    }

    let mut result = String::new();
    let pos = circle.iter().position(|&i| i == 1).unwrap();
    for i in pos + 1..max {
        result.push(char::from_digit(circle[i], 10).unwrap());
    }
    for i in 0..pos {
        result.push(char::from_digit(circle[i], 10).unwrap());
    }

    result
}

fn day_23b() -> u64 {
    let input = "792845136";
    let max = 1000000;
    let rounds = 10000000;

    let input: Vec<u64> = input
        .chars()
        .map(|c| c.to_digit(10).unwrap() as u64)
        .collect();

    let mut circle = HashMap::with_capacity(max as usize);
    circle.insert(input[0], (max, input[1]));
    for i in 1..input.len() - 1 {
        circle.insert(input[i], (input[i - 1], input[i + 1]));
    }
    let mut cur = input.len() as u64 + 1;
    circle.insert(input[input.len() - 1], (input[input.len() - 2], cur));
    circle.insert(cur, (input[input.len() - 1], cur + 1));
    cur += 1;
    for i in cur..max {
        circle.insert(i, (i - 1, i + 1));
    }
    circle.insert(max, (max - 1, input[0]));

    let mut cur = input[0];
    for _ in 1..=rounds {
        let t1 = circle[&cur].1;
        let t2 = circle[&t1].1;
        let t3 = circle[&t2].1;
        let t4 = circle[&t3].1;

        let mut dest = if cur == 1 { max } else { cur - 1 };
        while dest == t1 || dest == t2 || dest == t3 {
            dest = if dest == 1 { max } else { dest - 1 };
        }

        circle.insert(cur, (circle[&cur].0, t4));
        circle.insert(t4, (cur, circle[&t4].1));

        let n = circle[&dest].1;
        circle.insert(dest, (circle[&dest].0, t1));
        circle.insert(t1, (dest, t2));
        circle.insert(t3, (t2, n));
        circle.insert(n, (t3, circle[&n].1));

        cur = t4;
    }

    let first = circle[&1].1;
    let second = circle[&first].1;
    first * second
}

fn day_24() -> u32 {
    let lines = lines_to_vec("data/day_24.txt");

    #[derive(Debug)]
    enum Dir {
        E,
        SE,
        SW,
        W,
        NW,
        NE,
    }

    let mut input = vec![];
    for line in &lines {
        let mut v = vec![];
        let mut l: VecDeque<char> = line.chars().collect();
        if l.len() == 0 {
            continue;
        }
        while !l.is_empty() {
            match l.pop_front().unwrap() {
                'e' => v.push(Dir::E),
                'w' => v.push(Dir::W),
                's' => match l.pop_front().unwrap() {
                    'e' => v.push(Dir::SE),
                    'w' => v.push(Dir::SW),
                    x => panic!("wrong s{}", x),
                },
                'n' => match l.pop_front().unwrap() {
                    'e' => v.push(Dir::NE),
                    'w' => v.push(Dir::NW),
                    x => panic!("wrong n{}", x),
                },
                _ => {}
            }
        }
        input.push(v);
    }

    let mut tiles = HashMap::new();
    let mut black = 0;

    for line in &input {
        let mut x = 0;
        let mut y = 0;
        for dir in line {
            match dir {
                Dir::E => {
                    x -= 1;
                }
                Dir::SE => {
                    if y % 2 == 0 {
                        x -= 1;
                    }
                    y += 1;
                }
                Dir::SW => {
                    if !(y % 2 == 0) {
                        x += 1;
                    }
                    y += 1;
                }
                Dir::W => {
                    x += 1;
                }
                Dir::NE => {
                    if y % 2 == 0 {
                        x -= 1;
                    }
                    y -= 1;
                }
                Dir::NW => {
                    if !(y % 2 == 0) {
                        x += 1;
                    }
                    y -= 1;
                }
            }
        }
        let pos = y * 1000000 + x;
        let e = tiles.entry(pos).or_insert(false);
        if *e {
            black -= 1;
            *e = false;
        } else {
            black += 1;
            *e = true;
        }
    }

    black
}

fn day_24b() -> usize {
    let lines = lines_to_vec("data/day_24.txt");

    #[derive(Debug, Copy, Clone)]
    enum Dir {
        E,
        SE,
        SW,
        W,
        NW,
        NE,
    }
    const ALL_DIRECTIONS: [Dir; 6] = [Dir::E, Dir::SE, Dir::SW, Dir::W, Dir::NW, Dir::NE];

    let mut input = vec![];
    for line in &lines {
        let mut v = vec![];
        let mut l: VecDeque<char> = line.chars().collect();
        if l.len() == 0 {
            continue;
        }
        while !l.is_empty() {
            match l.pop_front().unwrap() {
                'e' => v.push(Dir::E),
                'w' => v.push(Dir::W),
                's' => match l.pop_front().unwrap() {
                    'e' => v.push(Dir::SE),
                    'w' => v.push(Dir::SW),
                    x => panic!("wrong s{}", x),
                },
                'n' => match l.pop_front().unwrap() {
                    'e' => v.push(Dir::NE),
                    'w' => v.push(Dir::NW),
                    x => panic!("wrong n{}", x),
                },
                _ => {}
            }
        }
        input.push(v);
    }

    fn hex_move(pos: (i32, i32), dir: Dir) -> (i32, i32) {
        let y = pos.0;
        let x = pos.1;
        match dir {
            Dir::E => (y, x - 1),
            Dir::SE => {
                if y % 2 == 0 {
                    (y + 1, x - 1)
                } else {
                    (y + 1, x)
                }
            }
            Dir::SW => {
                if !(y % 2 == 0) {
                    (y + 1, x + 1)
                } else {
                    (y + 1, x)
                }
            }
            Dir::W => (y, x + 1),
            Dir::NE => {
                if y % 2 == 0 {
                    (y - 1, x - 1)
                } else {
                    (y - 1, x)
                }
            }
            Dir::NW => {
                if !(y % 2 == 0) {
                    (y - 1, x + 1)
                } else {
                    (y - 1, x)
                }
            }
        }
    }

    fn count_black(src: &HashSet<(i32, i32)>, pos: (i32, i32)) -> i32 {
        let mut black = 0;
        for &dir in &ALL_DIRECTIONS {
            let neighbor = hex_move(pos, dir);
            if src.contains(&neighbor) {
                black += 1;
            }
        }
        black
    }

    let mut tiles = HashSet::new();
    for line in &input {
        let mut pos = (0, 0);
        for &dir in line {
            pos = hex_move(pos, dir);
        }
        if tiles.contains(&pos) {
            tiles.remove(&pos);
        } else {
            tiles.insert(pos);
        }
    }

    let days = 100;
    let mut tiles2 = HashSet::new();
    let mut last = 0;

    for day in 1..=days {
        let (src, dst) = if day % 2 == 0 {
            (&tiles2, &mut tiles)
        } else {
            (&tiles, &mut tiles2)
        };
        dst.clear();
        for &k in src {
            let black = count_black(src, k);
            if !(black == 0 || black > 2) {
                dst.insert(k);
            }
            for &dir in &ALL_DIRECTIONS {
                let pos = hex_move(k, dir);
                if src.contains(&pos) {
                    continue;
                }
                if count_black(src, pos) == 2 {
                    dst.insert(pos);
                }
            }
        }
        last = dst.len();
    }

    last
}

fn day_25() -> i64 {
    let card_pub_key = 3_469_259;
    let door_pub_key = 13_170_438;

    fn transform(subject: i64, loop_size: usize) -> i64 {
        let mut i = 1;
        for _ in 0..loop_size {
            i = i * subject;
            i = i % 20_201_227;
        }
        i
    }

    fn guess_loop_size(pub_key: i64) -> usize {
        let mut i = 1;
        for ls in 1..1_000_000_000 {
            i = i * 7;
            i = i % 20_201_227;
            if i == pub_key {
                return ls;
            }
        }
        panic!("cannot guess the loop size");
    }

    let card_loop_size = guess_loop_size(card_pub_key);
    let res = transform(door_pub_key, card_loop_size);

    res
}

fn day_25b() -> i32 {
    println!("I know the basics of Rust 😄");
    1
}
