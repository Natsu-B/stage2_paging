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

const UART_DR: usize = 0x000;
const UART_FR: usize = 0x018;

pub fn mmio_read(offset: usize, _access_width: u64) -> Result<u64, ()> {
    match offset {
        UART_FR => Ok(0),
        _ => Err(()),
    }
}

pub fn mmio_write(offset: usize, _access_width: u64, value: u64) -> Result<(), ()> {
    match offset {
        UART_DR => {
            print!("{}", value as u8 as char);
            Ok(())
        }
        _ => Err(()),
    }
}
