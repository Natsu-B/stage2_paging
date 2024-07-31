// Copyright (c) 2022 RIKEN
// Copyright (c) 2022 National Institute of Advanced Industrial Science and Technology (AIST)
// All rights reserved.
//
// This software is released under the MIT License.
// http://opensource.org/licenses/mit-license.php

//Copyright 2023 Manami Mori
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.

//!
//! Paging
//!

use core::default;

use crate::{allocate_memory, bitmask, console::print, cpu::*};

pub const PAGE_SHIFT: usize = 12;
pub const PAGE_SIZE: usize = 1 << PAGE_SHIFT;
pub const PAGE_MASK: usize = !(PAGE_SIZE - 1);
pub const STAGE_2_PAGE_SHIFT: usize = 12;
pub const STAGE_2_PAGE_SIZE: usize = 1 << STAGE_2_PAGE_SHIFT;
pub const STAGE_2_PAGE_MASK: usize = !(STAGE_2_PAGE_SIZE - 1);
pub const PAGE_TABLE_SIZE: usize = 0x1000;

pub const PAGE_DESCRIPTORS_UPPER_ATTRIBUTES_OFFSET: u64 = 50;
pub const PAGE_DESCRIPTORS_CONTIGUOUS: u64 = 1 << 52;
pub const PAGE_DESCRIPTORS_NX_BIT_OFFSET: u64 = 54;

pub const PAGE_DESCRIPTORS_NT: u64 = 1 << 16;
pub const PAGE_DESCRIPTORS_AF_BIT_OFFSET: u64 = 10;
pub const PAGE_DESCRIPTORS_AF: u64 = 1 << PAGE_DESCRIPTORS_AF_BIT_OFFSET;
pub const PAGE_DESCRIPTORS_SH_BITS_OFFSET: u64 = 8;
pub const PAGE_DESCRIPTORS_SH_INNER_SHAREABLE: u64 = 0b11 << PAGE_DESCRIPTORS_SH_BITS_OFFSET;
pub const PAGE_DESCRIPTORS_AP_BITS_OFFSET: u64 = 6;

pub const MEMORY_PERMISSION_READABLE_BIT: u8 = 0;
pub const MEMORY_PERMISSION_WRITABLE_BIT: u8 = 1;
pub const MEMORY_PERMISSION_EXECUTABLE_BIT: u8 = 2;

pub const PAGE_DESCRIPTORS_AP: u64 = 0b11 << PAGE_DESCRIPTORS_AP_BITS_OFFSET;
pub const PAGE_DESCRIPTORS_ATTR_BITS_OFFSET: u64 = 2;
pub const PAGE_DESCRIPTORS_ATTR: u64 = 0b1111 << PAGE_DESCRIPTORS_ATTR_BITS_OFFSET;

//4KB paging
pub fn setup_stage_2_translation() -> Result<(), ()> {
    let ps = get_id_aa64mmfr0_el1() & ID_AA64MMFR0_EL1_PARANGE;
    println!("PS: {:b}", ps);
    let (t0sz, table_level) = match ps {
        0b000 => (32u8, 1i8), //32bit
        0b001 => (28u8, 1i8), //36bit
        0b010 => (24u8, 1i8), //40bit
        0b011 => (22u8, 0i8), //42bit
        0b100 => (20u8, 0i8), //44bit
        0b101 => (16u8, 0i8), //48bit
        _ => (16u8, 0i8), //52,56bit //arm ref 7912 6580 t0szとtable_levelはconcated page tableと初期化に必要
    };
    let mut physical_address = 0;
    let sl0 = if table_level == 1 { 0b01u64 } else { 0b10u64 };
    let number_of_tables = calculate_number_of_concatenated_page_tables(t0sz, table_level); //あまりここはよくわからなかったからとりまMilvusVisorからコピペ
    let table_address: usize =
        allocate_page_table_for_stage_2(table_level, t0sz, true, number_of_tables)?; //返却型が Result<usize, ()>だから?でusize型のみにしてる?
    let page_table = unsafe {
        //最初から 64bit number_of_tables * 512 だけ並べる配列を作ってる
        core::slice::from_raw_parts_mut(
            table_address as *mut u64,
            (PAGE_TABLE_SIZE * number_of_tables as usize) / core::mem::size_of::<u64>(),
        )
    };
    for e in page_table {
        *e = 0;
    }
    //_setup_stage_2_translation(table_address, table_level, t0sz, number_of_tables as usize, &mut physical_address)?;
    let vtcr_el2: u64 = VTCR_EL2_RES1
        | ((ps as u64) << VTCR_EL2_PS_BITS_OFFSET)
        | (0 << VTCR_EL2_TG0_BITS_OFFSET)
        | (0b11 << VTCR_EL2_SH0_BITS_OFFSET)
        | (0b11 << VTCR_EL2_ORG0_BITS_OFFSET)
        | (0b11 << VTCR_EL2_IRG0_BITS_OFFSET)
        | (sl0 << VTCR_EL2_SL0_BITS_OFFSET)
        | ((t0sz as u64) << VTCR_EL2_T0SZ_BITS_OFFSET);
    //VTCR_EL2 をセットする よくわからん～
    set_vtcr_el2(vtcr_el2);
    //VTTBR_EL2 (≒CR3)をセットする
    set_vttbr_el2(table_address as u64);
    //HCR_EL2の設定して戻る 31、41bit目のみ有効
    Ok(())
}

pub fn map_address_stage2(mut physical_address: usize, mut map_size: usize) -> Result<(), ()> {
    if (map_size & ((1usize << PAGE_SHIFT) - 1)) != 0 {
        println!("Map size is not aligned.");
        return Err(());
    }
    let mut num_of_pages = map_size / PAGE_SIZE;
    let page_table_address = get_vttbr_el2() as usize;
    let vtcr_el2 = get_vtcr_el2();
    let sl0 = ((vtcr_el2 & VTCR_EL2_SL0) >> VTCR_EL2_SL0_BITS_OFFSET) as u8;
    let t0sz = ((vtcr_el2 & VTCR_EL2_T0SZ) >> VTCR_EL2_T0SZ_BITS_OFFSET) as u8;
    let table_level: i8 = match sl0 {
        0b00 => 2,
        0b01 => 1,
        0b10 => 0,
        0b11 => 3,
        _ => unreachable!(),
    };
    println!("get table level {:#X}", table_level);
    println!(
        "first num_of_entries: {:#X}",
        (calculate_number_of_concatenated_page_tables(t0sz, table_level) as usize) * 512
    );
    _setup_stage_2_translation(
        page_table_address,
        table_level,
        t0sz,
        calculate_number_of_concatenated_page_tables(t0sz, table_level) as usize,
        &mut physical_address,
        &mut num_of_pages,
    )?;
    flush_tlb_el1();
    Ok(())
}

/*
    table_level: i8 から初めてtable level 3まで 実行
    setup_stage2_translationの部分でのallocate_page_table~では、最上位ページのみallocateしてるから初期化処理が終わったあと次のページをallocateしないと
    初期化処理をしたい、、、どうしよ
    table_levelを table_address から再帰的に呼び出すたびに+1してって 3 になれば終了
    blockpagingをやりたい
*/
fn _setup_stage_2_translation(
    table_address: usize,
    table_level: i8,
    t0sz: u8,
    number_of_tables: usize,
    physical_address: &mut usize,
    num_of_pages: &mut usize,
) -> Result<(), ()> {
    let mut i = 0;
    let shift_level = table_level_to_table_shift(STAGE_2_PAGE_SHIFT, table_level);
    let table_index = (*physical_address >> shift_level)
        & (((PAGE_TABLE_SIZE * number_of_tables) / core::mem::size_of::<u64>()) - 1);
    if table_level < 3 {
        println!("{table_level}: {shift_level}: {table_index}");
    }
    let page_table = unsafe {
        //最初から 64bit number_of_tables * 512 だけ並べる配列を作ってる
        core::slice::from_raw_parts_mut(
            table_address as *mut u64,
            (PAGE_TABLE_SIZE * number_of_tables) / core::mem::size_of::<u64>(),
        )
    };

    if (3 == table_level) {
        //page_table3(bottom)の初期化処理
        for e in page_table[table_index..].iter_mut() {
            *e = (*physical_address as u64)
                | PAGE_DESCRIPTORS_AF
                | PAGE_DESCRIPTORS_SH_INNER_SHAREABLE
                | PAGE_DESCRIPTORS_AP
                | PAGE_DESCRIPTORS_ATTR
                | 0b11; //初期化するよ
            *physical_address += 1 << shift_level;
            *num_of_pages -= 1;
            if *num_of_pages == 0 {
                return Ok(());
            }
        }
    } else {
        //その他page_tableの初期化
        for e in page_table[table_index..].iter_mut() {
            let next_table_address: usize;
            if *e & 0b11 == 0b11 {
                next_table_address = (*e as usize) & !0b11;
                println!("Level{}[{}]: Exists", table_level, i);
            } else {
                next_table_address =
                    allocate_page_table_for_stage_2(table_level + 1, t0sz, false, 1)?;
                println!("Level{}[{}]: Allocated", table_level, i);
            }
            i += 1;
            _setup_stage_2_translation(
                next_table_address,
                table_level + 1,
                t0sz,
                1,
                physical_address,
                num_of_pages,
            )?;
            *e = (next_table_address as u64) | 0b11; //初期化するよ
            if *num_of_pages == 0 {
                return Ok(());
            }
        }
    }
    //MilvusVisorはブロックページングを採用しているから、これと同じようにページングするとメモリを使いすぎる
    /*
    if table_level >= 1 {
        for e in page_table {
            *e = (*physical_address as u64) | 2045;
            *physical_address += 1 << shift_level;
        }
    } else {
        for e in page_table {
            let next_table_address =
                allocate_page_table_for_stage_2(table_level + 1, t0sz, false, 1)?;
            _setup_stage_2_translation(
                next_table_address,
                table_level + 1,
                t0sz,
                1,
                physical_address,
            )?;
            *e = (next_table_address as u64) | 0b11;
        }
    }*/
    return Ok(());
}

pub const fn table_level_to_table_shift(
    translation_granule_shift: usize,
    table_level: i8,
) -> usize {
    translation_granule_shift + 9 * (3 - table_level) as usize
}

pub const fn calculate_number_of_concatenated_page_tables(
    t0sz: u8,
    initial_lookup_level: i8,
) -> u8 {
    if t0sz > (43 - ((3 - initial_lookup_level) as u8) * 9) {
        1
    } else {
        2u8.pow(((43 - ((3 - initial_lookup_level) as u8) * 9) - t0sz) as u32)
    }
}

/// Allocate page table for stage 2 with suitable address alignment
#[inline(always)]
fn allocate_page_table_for_stage_2(
    look_up_level: i8,
    t0sz: u8,
    is_for_ttbr: bool, //translate table base register の略でこれはx64 では CR3レジスタ
    number_of_tables: u8,
) -> Result<usize, ()> {
    assert_ne!(number_of_tables, 0);
    let alignment = if is_for_ttbr {
        ((64 - ((PAGE_SHIFT - 3) as usize * (4 - look_up_level) as usize) - t0sz as usize).max(4))
            .min(12)
            + (number_of_tables as usize - 1)
    } else {
        assert_eq!(number_of_tables, 1);
        STAGE_2_PAGE_SHIFT
    };
    match allocate_memory(number_of_tables as usize, Some(alignment)) {
        Ok(address) => Ok(address),
        Err(err) => {
            println!("Failed to allocate the page table: {:?}", err);
            Err(())
        }
    }
}
