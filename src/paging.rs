// Copyright (c) 2022 RIKEN
// Copyright (c) 2022 National Institute of Advanced Industrial Science and Technology (AIST)
// All rights reserved.
//
// This software is released under the MIT License.
// http://opensource.org/licenses/mit-license.php

//!
//! Paging
//!

use core::default;

use crate::{allocate_memory, bitmask, cpu::*};

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

//4KB paging
pub fn setup_stage_2_translation() -> Result<(), ()> {
    let ps = get_id_aa64mmfr0_el1() & ID_AA64MMFR0_EL1_PARANGE;
    let (t0sz, table_level) = match ps {
        0b000 => (32u8, 1i8),//32bit
        0b001 => (28u8, 1i8),//36bit
        0b010 => (24u8, 1i8),//40bit
        0b011 => (22u8, 1i8),//42bit
        0b100 => (20u8, 0i8),//44bit
        0b101 => (16u8, 0i8),//48bit
        _ => (16u8, 0i8)//52,56bit //arm ref 7912 6580 t0szとtable_levelはconcated page tableと初期化に必要
    };
    let mut physical_address = 0;
    let sl0 = if table_level == 1 { 0b01u64 } else { 0b10u64 };
    let number_of_tables = calculate_number_ofconcatenated_page_tables(t0sz, table_level);//あまりここはよくわからなかったからとりまMilvusVisorからコピペ
    let table_address: usize =
        allocate_page_table_for_stage_2(table_level, t0sz, true, number_of_tables)?;//返却型が Result<usize, ()>だから?でusize型のみにしてる?
    _setup_stage_2_translation(table_address, table_level, t0sz, number_of_tables as usize, &mut physical_address)?;
    let vtcr_el2: u64 = VTCR_EL2_RES1 
        | ((ps as u64) << VTCR_EL2_PS_BITS_OFFSET) 
        | (0 << VTCR_EL2_TG0_BITS_OFFSET)
        | (0b11 << VTCR_EL2_SH0_BITS_OFFSET) 
        | (0b11 << VTCR_EL2_ORG0_BITS_OFFSET) 
        | (0b11 << VTCR_EL2_IRG0_BITS_OFFSET) 
        | (sl0  << VTCR_EL2_SL0_BITS_OFFSET) 
        | ((t0sz as u64) << VTCR_EL2_T0SZ_BITS_OFFSET);
    //VTCR_EL2 をセットする よくわからん～
    set_vtcr_el2(vtcr_el2);
    //VTTBR_EL2 (≒CR3)をセットする
    set_vttbr_el2(table_address as u64);
    //HCR_EL2の設定して戻る 31、41bit目のみ有効
    Ok(())
}

/*
    table_level: i8 から初めてtable level 3まで 実行
    setup_stage2_translationの部分でのallocate_page_table~では、最上位ページのみallocateしてるから初期化処理が終わったあと次のページをallocateしないと
    初期化処理をしたい、、、どうしよ
    table_levelを table_address から再帰的に呼び出すたびに+1してって 3 になれば終了
*/
fn _setup_stage_2_translation(
    table_address: usize,
    table_level: i8,
    t0sz: u8,
    number_of_tables: usize,
    physical_address: &mut usize
) -> Result<(), ()>{
    let page_table = unsafe {//多分最初から 64bit ごとに並べる配列を作ってる
        core::slice::from_raw_parts_mut(
            table_address as *mut u64,
            (PAGE_TABLE_SIZE * number_of_tables) / core::mem::size_of::<u64>(),
        )
    };
    if(3 == table_level){
        //page_table3(bottom)の初期化処理
        for e in page_table {
            *e = (*physical_address as u64) | 2045 ; //初期化するよ
            *physical_address += 1 << 9;
        }
    }else{
        //その他page_tableの初期化
        for e in page_table {
            let next_table_address =
                allocate_page_table_for_stage_2(table_level + 1, t0sz, false, 1)?;
            _setup_stage_2_translation(
                next_table_address,
                1,
                t0sz,
                (table_level + 1) as usize,
                physical_address,

            )?;
            *e = (next_table_address as u64) | 0b11;
        }
    }
    return Ok(())
}

fn calculate_number_ofconcatenated_page_tables(
    t0sz: u8,
    table_level: i8,
)
     -> u8{
        if t0sz > (43 - ((3 - table_level) as u8) * 9) {
            1
        } else {
            2u8.pow(((43 - ((3 - table_level) as u8) * 9) - t0sz) as u32)   
     }
}

/// Allocate page table for stage 2 with suitable address alignment
#[inline(always)]
fn allocate_page_table_for_stage_2(
    look_up_level: i8,
    t0sz: u8,
    is_for_ttbr: bool,//translate table base register の略でこれはx64 では CR3レジスタ
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