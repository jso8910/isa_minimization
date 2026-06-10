use std::{error::Error, fs};

use liberty_db::{DefaultCtx, Library, pin::Direction};

use crate::bit::LookupTable;

#[derive(Debug)]
pub struct StandardCellLibrary {
    pub cells: Vec<StandardCell>
}

impl StandardCellLibrary {
    pub fn new(filename: &str) -> Result<Self, Box<dyn Error>> {
        let lib_text = fs::read_to_string(filename)?;
        let library = Library::<DefaultCtx>::parse_lib(&lib_text, None)?;
        let mut cells = vec![];

        for cell in library.cell.iter() {
            let mut inputs = vec![];
            let mut outs = vec![];
            let mut outs_raw = vec![];
            let is_sequential = !cell.ff.is_empty() || !cell.ff_bank.is_empty() ||
                                            !cell.latch.is_empty() || !cell.latch_bank.is_empty() ||
                                            cell.statetable.is_some() || cell.memory.is_some();


            for pin in cell.pin.iter() {
                match pin.direction {
                    Some(Direction::Input) => inputs.push(Pin::new_in(pin.name.clone())),
                    Some(Direction::Output) => outs_raw.push(pin),
                    Some(Direction::Internal) => continue,    // ignore internal pins
                    d => panic!("Unsupported pin direction {:?}", d)
                }
            }

            for out_pin in outs_raw.into_iter() {
                if is_sequential {
                    outs.push(Pin::new_seq(out_pin.name.clone()));
                } else {
                    outs.push(
                        Pin::new_out(
                            out_pin.name.clone(),
                            out_pin.function.as_ref().unwrap().to_string().as_str(),
                            &inputs
                        )
                    );
                }
            }

            let pins = inputs.into_iter().chain(outs).collect();
            cells.push(StandardCell::new(cell.name.clone(), pins, is_sequential));
        }
        Ok(Self { cells })
    }
}

#[derive(Debug)]
pub struct StandardCell {
    pub name: String,
    pub pins: Vec<Pin>,
    pub is_sequential: bool,
}

impl StandardCell {
    pub fn new(name: String, pins: Vec<Pin>, is_sequential: bool) -> Self {
        let has_seq_pins = pins.iter().any(|p| matches!(p, Pin::SequentialOutput { .. }));
        assert_eq!(has_seq_pins, is_sequential, "Iff `is_sequential`, `pins` should have at least one SequentialOutput pin");
        Self {
            name,
            pins,
            is_sequential
        }
    }
}

#[derive(Debug)]
pub enum Pin {
    Input { name: String },
    Output { name: String, function: LookupTable },
    SequentialOutput { name: String }
}

impl Pin {
    pub fn new_out(name: String, func_str: &str, inputs: &Vec<Pin>) -> Self {
        Self::Output {
            name,
            function: LookupTable::new_from_string(func_str, inputs.iter().map(|i| {
                let Pin::Input { name } = i else { panic!("Inputs to Pin::Output must be of type Pin::Input") };
                name.as_str()
            }).collect())
        }
    }

    pub fn new_seq(name: String) -> Self {
        Self::SequentialOutput { name }
    }

    pub fn new_in(name: String) -> Self {
        Self::Input { name }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn test() {
    //     StandardCellLibrary::new("examples/NangateOpenCellLibrary_typical.lib");
    //     panic!();
    // }
}