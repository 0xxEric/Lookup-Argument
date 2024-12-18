

use rand::seq::SliceRandom; // 引入随机选择
use rand::thread_rng; // 引入随机数生成器
use std::collections::HashSet;

fn gengerate_table_and_lookup() {
    let k = 3; // 您可以根据需要修改 k 的值
    let size = 1 << k; // size = 2^k

    // 生成 table 数组
    let table: Vec<u32> = (0..size).collect();

    // 生成 lookup 数组
    let mut lookup: Vec<u32> = Vec::with_capacity(size);
    let mut rng = thread_rng();

    // 随机选择 2^(k-1) 个不同的值
    let distinct_count = size / 2;
    let mut distinct_values: HashSet<u32> = HashSet::new();

    // 保证 distinct_values 中至少有 2^(k-1) 个不同的值
    while distinct_values.len() < distinct_count as usize {
        let value = table.choose(&mut rng).unwrap();
        distinct_values.insert(*value);
    }

    // 将 distinct_values 的内容填充至 lookup 数组
    let distinct_values: Vec<u32> = distinct_values.into_iter().collect();
    for _ in 0..size {
        let value = distinct_values.choose(&mut rng).unwrap();
        lookup.push(*value);
    }

    // 打印结果
    println!("Table: {:?}", table);
    println!("Lookup: {:?}", lookup);
}