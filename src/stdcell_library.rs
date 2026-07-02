use std::{collections::HashMap, error::Error, fs};

use liberty_db::{DefaultCtx, Library, pin::Direction};

use crate::bit::LookupTable;

#[derive(Debug)]
pub struct StandardCellLibrary {
    pub cells: HashMap<String, StandardCell>,
}

impl StandardCellLibrary {
    pub fn new(filename: &str) -> Result<Self, Box<dyn Error>> {
        let lib_text = fs::read_to_string(filename)?;
        let library = Library::<DefaultCtx>::parse_lib(&lib_text, None)?;
        let mut cells = HashMap::new();

        for cell in library.cell.iter() {
            let mut inputs = vec![];
            let mut outs = vec![];
            let mut outs_raw = vec![];
            let is_sequential = !cell.ff.is_empty()
                || !cell.ff_bank.is_empty()
                || !cell.latch.is_empty()
                || !cell.latch_bank.is_empty()
                || cell.statetable.is_some()
                || cell.memory.is_some();

            for pin in cell.pin.iter() {
                match pin.direction {
                    Some(Direction::Input) => inputs.push(Pin::new_in(pin.name.clone())),
                    Some(Direction::Output) => outs_raw.push(pin),
                    Some(Direction::Internal) => continue, // ignore internal pins
                    d => panic!("Unsupported pin direction {:?}", d),
                }
            }

            for out_pin in outs_raw.into_iter() {
                if is_sequential {
                    outs.push(Pin::new_seq(out_pin.name.clone()));
                } else {
                    outs.push(Pin::new_out(
                        out_pin.name.clone(),
                        out_pin.function.as_ref().unwrap().to_string().as_str(),
                        &inputs,
                    ));
                }
            }

            let pins = inputs.into_iter().chain(outs).collect();
            cells.insert(
                cell.name.clone(),
                StandardCell::new(cell.name.clone(), pins, is_sequential),
            );
        }
        Ok(Self { cells })
    }
}

#[derive(Debug)]
pub struct StandardCell {
    pub name: String,
    pub pins: Vec<Pin>,

    // New cached views
    pub input_pins: Vec<String>,
    pub output_pins: Vec<OutputPin>,
    pub sequential_output_pins: Vec<String>,

    pub is_sequential: bool,
}

impl StandardCell {
    pub fn new(name: String, pins: Vec<Pin>, is_sequential: bool) -> Self {
        let input_pins = pins
            .iter()
            .filter_map(|p| match p {
                Pin::Input { name } => Some(name.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();

        let output_pins = pins
            .iter()
            .filter_map(|p| match p {
                Pin::Output { name, function } => Some(OutputPin {
                    name: name.clone(),
                    function: function.clone(),
                }),
                _ => None,
            })
            .collect::<Vec<_>>();

        let sequential_output_pins = pins
            .iter()
            .filter_map(|p| match p {
                Pin::SequentialOutput { name } => Some(name.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();

        let has_seq_pins = !sequential_output_pins.is_empty();

        assert_eq!(
            has_seq_pins, is_sequential,
            "Iff `is_sequential`, `pins` should have at least one SequentialOutput pin"
        );

        Self {
            name,
            pins,
            input_pins,
            output_pins,
            sequential_output_pins,
            is_sequential,
        }
    }

    pub fn has_pin(&self, name: &str) -> bool {
        self.input_pins.iter().any(|p| p == name)
            || self.output_pins.iter().any(|p| p.name == name)
            || self.sequential_output_pins.iter().any(|p| p == name)
    }
}

#[derive(Debug, Clone)]
pub struct OutputPin {
    pub name: String,
    pub function: LookupTable,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Pin {
    Input { name: String },
    Output { name: String, function: LookupTable },
    SequentialOutput { name: String },
}

impl Pin {
    pub fn new_out(name: String, func_str: &str, inputs: &Vec<Pin>) -> Self {
        Self::Output {
            name,
            function: LookupTable::new_from_string(
                func_str,
                inputs
                    .iter()
                    .map(|i| {
                        let Pin::Input { name } = i else {
                            panic!("Inputs to Pin::Output must be of type Pin::Input")
                        };
                        name.as_str()
                    })
                    .collect(),
            ),
        }
    }

    pub fn new_seq(name: String) -> Self {
        Self::SequentialOutput { name }
    }

    pub fn new_in(name: String) -> Self {
        Self::Input { name }
    }

    pub fn name(&self) -> &str {
        match self {
            Pin::Input { name } => name,
            Pin::Output { name, function: _ } => name,
            Pin::SequentialOutput { name } => name,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pin_name_returns_name_for_each_pin_kind() {
        let input = Pin::new_in("A".to_string());
        let output = Pin::new_out("Z".to_string(), "A", &vec![input.clone()]);
        let sequential = Pin::new_seq("Q".to_string());

        assert_eq!(input.name(), "A");
        assert_eq!(output.name(), "Z");
        assert_eq!(sequential.name(), "Q");
    }
}
