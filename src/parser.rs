use pest::Parser;
use pest::iterators::Pair;
use pest_derive::Parser;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Parser)]
#[grammar = "verilog_netlist.pest"]
struct MinNetlistParser;

#[derive(Debug, Error)]
pub enum NetlistError {
    #[error("parse error: {0}")]
    Parse(String),

    #[error("expected exactly one module, found {0}")]
    WrongModuleCount(usize),

    #[error("unsupported concatenation in expression near byte {start}")]
    UnsupportedConcat { start: usize },

    #[error("unsupported slice / part-select in expression near byte {start}")]
    UnsupportedPartSelect { start: usize },

    #[error("positional instance connections are not supported near byte {start}")]
    UnsupportedPositionalConnection { start: usize },

    #[error("internal parser error: {0}")]
    Internal(&'static str),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleNetlist {
    pub name: String,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    pub wires: Vec<String>,
    pub instances: HashMap<String, Instance>,
    pub assignments: Vec<Assign>,
}

impl ModuleNetlist {
    pub fn all_declared_nets(&self) -> impl Iterator<Item = &String> {
        self.inputs
            .iter()
            .chain(self.outputs.iter())
            .chain(self.wires.iter())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instance {
    pub cell_type: String,
    pub name: String,
    pub connections: HashMap<String, Option<Expr>>,
    pub parameters: HashMap<String, Option<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assign {
    pub lhs: Expr,
    pub rhs: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// A scalar net reference.
    ///
    /// Examples:
    /// - "a"
    /// - "bus[3]"
    /// - "\\escaped.name[3]"
    Net(String),

    /// A Verilog constant.
    ///
    /// Examples:
    /// - "1'b0"
    /// - "32'hdead_beef"
    /// - "0"
    Const(String),

    Unary {
        op: String,
        rhs: Box<Expr>,
    },

    Binary {
        lhs: Box<Expr>,
        op: String,
        rhs: Box<Expr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Range {
    msb: usize,
    lsb: usize,
}

pub fn parse_netlist(src: &str) -> Result<ModuleNetlist, NetlistError> {
    let file = MinNetlistParser::parse(Rule::file, src)
        .map_err(|e| NetlistError::Parse(e.to_string()))?
        .next()
        .ok_or(NetlistError::Internal("missing file pair"))?;

    let modules: Vec<_> = file
        .into_inner()
        .filter(|p| p.as_rule() == Rule::module_decl)
        .collect();

    if modules.len() != 1 {
        return Err(NetlistError::WrongModuleCount(modules.len()));
    }

    visit_module_declaration(modules.into_iter().next().unwrap())
}

fn visit_module_declaration(pair: Pair<Rule>) -> Result<ModuleNetlist, NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::module_decl);

    let mut inner = pair.into_inner();

    let name = inner
        .find(|p| p.as_rule() == Rule::ident)
        .ok_or(NetlistError::Internal("module missing name"))?
        .as_str()
        .to_string();

    let mut module = ModuleNetlist {
        name,
        inputs: Vec::new(),
        outputs: Vec::new(),
        wires: Vec::new(),
        instances: HashMap::new(),
        assignments: Vec::new(),
    };

    for item in inner {
        match item.as_rule() {
            Rule::port_header => {
                visit_port_header(item, &mut module)?;
            }
            Rule::module_item => {
                visit_module_item(item, &mut module)?;
            }
            Rule::attribute | Rule::directive => {
                // Ignore attributes and directives.
            }
            _ => {}
        }
    }

    Ok(module)
}

fn visit_port_header(pair: Pair<Rule>, module: &mut ModuleNetlist) -> Result<(), NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::port_header);

    for item in pair.into_inner() {
        for child in item.into_inner() {
            if child.as_rule() == Rule::port_decl_inline {
                visit_inline_port_decl(child, module)?;
            }
        }
    }

    Ok(())
}

fn visit_inline_port_decl(
    pair: Pair<Rule>,
    module: &mut ModuleNetlist,
) -> Result<(), NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::port_decl_inline);

    let mut dir: Option<String> = None;
    let mut range: Option<Range> = None;
    let mut name: Option<String> = None;

    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::port_dir => {
                dir = Some(child.as_str().to_string());
            }
            Rule::range => {
                range = Some(parse_range(child)?);
            }
            Rule::ident => {
                name = Some(child.as_str().to_string());
            }
            Rule::net_kind => {
                // Ignore. Example: output wire y;
            }
            _ => {}
        }
    }

    let dir = dir.ok_or(NetlistError::Internal("inline port missing direction"))?;
    let name = name.ok_or(NetlistError::Internal("inline port missing name"))?;

    for scalar_name in expand_decl_name(&name, range) {
        match dir.as_str() {
            "input" => push_unique(&mut module.inputs, scalar_name),
            "output" => push_unique(&mut module.outputs, scalar_name),
            "inout" => {
                push_unique(&mut module.inputs, scalar_name.clone());
                push_unique(&mut module.outputs, scalar_name);
            }
            _ => {}
        }
    }

    Ok(())
}

fn visit_module_item(pair: Pair<Rule>, module: &mut ModuleNetlist) -> Result<(), NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::module_item);

    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::declaration => {
                visit_declaration(child, module)?;
            }
            Rule::assign_stmt => {
                module.assignments.push(visit_assign(child)?);
            }
            Rule::instance => {
                let instance = visit_instance(child)?;
                module.instances.insert(instance.name.clone(), instance);
            }
            Rule::attribute | Rule::directive => {
                // Ignore.
            }
            _ => {}
        }
    }

    Ok(())
}

fn visit_declaration(pair: Pair<Rule>, module: &mut ModuleNetlist) -> Result<(), NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::declaration);

    let decl = pair
        .into_inner()
        .next()
        .ok_or(NetlistError::Internal("empty declaration"))?;

    match decl.as_rule() {
        Rule::port_decl => visit_port_decl(decl, module),
        Rule::net_decl => visit_net_decl(decl, module),
        _ => Err(NetlistError::Internal("bad declaration child")),
    }
}

fn visit_port_decl(pair: Pair<Rule>, module: &mut ModuleNetlist) -> Result<(), NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::port_decl);

    let mut dir: Option<String> = None;
    let mut range: Option<Range> = None;
    let mut names: Vec<String> = Vec::new();

    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::port_dir => {
                dir = Some(child.as_str().to_string());
            }
            Rule::range => {
                range = Some(parse_range(child)?);
            }
            Rule::ident_list => {
                names = parse_ident_list(child);
            }
            Rule::net_kind => {
                // Ignore. Example: output wire y;
            }
            _ => {}
        }
    }

    let dir = dir.ok_or(NetlistError::Internal("port decl missing direction"))?;

    for name in names {
        for scalar_name in expand_decl_name(&name, range) {
            match dir.as_str() {
                "input" => push_unique(&mut module.inputs, scalar_name),
                "output" => push_unique(&mut module.outputs, scalar_name),
                "inout" => {
                    push_unique(&mut module.inputs, scalar_name.clone());
                    push_unique(&mut module.outputs, scalar_name);
                }
                _ => {}
            }
        }
    }

    Ok(())
}

fn visit_net_decl(pair: Pair<Rule>, module: &mut ModuleNetlist) -> Result<(), NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::net_decl);

    let mut kind: Option<String> = None;
    let mut range: Option<Range> = None;
    let mut names: Vec<String> = Vec::new();

    for child in pair.into_inner() {
        match child.as_rule() {
            Rule::net_kind => {
                kind = Some(child.as_str().to_string());
            }
            Rule::range => {
                range = Some(parse_range(child)?);
            }
            Rule::ident_list => {
                names = parse_ident_list(child);
            }
            _ => {}
        }
    }

    let kind = kind.ok_or(NetlistError::Internal("net decl missing kind"))?;

    if matches!(kind.as_str(), "wire" | "tri" | "supply0" | "supply1") {
        for name in names {
            for scalar_name in expand_decl_name(&name, range) {
                push_unique(&mut module.wires, scalar_name);
            }
        }
    }

    Ok(())
}

fn parse_ident_list(pair: Pair<Rule>) -> Vec<String> {
    debug_assert_eq!(pair.as_rule(), Rule::ident_list);

    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::ident)
        .map(|p| p.as_str().to_string())
        .collect()
}

fn parse_range(pair: Pair<Rule>) -> Result<Range, NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::range);

    let nums: Result<Vec<usize>, _> = pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::number)
        .map(|p| p.as_str().parse::<usize>())
        .collect();

    let nums = nums.map_err(|_| NetlistError::Internal("bad range number"))?;

    if nums.len() != 2 {
        return Err(NetlistError::Internal("bad range"));
    }

    Ok(Range {
        msb: nums[0],
        lsb: nums[1],
    })
}

fn expand_decl_name(name: &str, range: Option<Range>) -> Vec<String> {
    match range {
        None => vec![name.to_string()],

        Some(r) => {
            let lo = r.msb.min(r.lsb);
            let hi = r.msb.max(r.lsb);

            (lo..=hi).map(|i| format!("{name}[{i}]")).collect()
        }
    }
}

fn push_unique(v: &mut Vec<String>, name: String) {
    if !v.iter().any(|x| x == &name) {
        v.push(name);
    }
}

fn visit_assign(pair: Pair<Rule>) -> Result<Assign, NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::assign_stmt);

    let exprs: Vec<_> = pair
        .into_inner()
        .filter(|p| p.as_rule() == Rule::expr)
        .collect();

    if exprs.len() != 2 {
        return Err(NetlistError::Internal("assign did not have lhs and rhs"));
    }

    Ok(Assign {
        lhs: visit_expr(exprs[0].clone())?,
        rhs: visit_expr(exprs[1].clone())?,
    })
}

fn visit_instance(pair: Pair<Rule>) -> Result<Instance, NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::instance);

    let mut children = pair.into_inner();

    let cell_type = children
        .next()
        .ok_or(NetlistError::Internal("instance missing cell type"))?
        .as_str()
        .to_string();

    let mut parameters = HashMap::new();

    let next = children
        .next()
        .ok_or(NetlistError::Internal("instance missing name"))?;

    let name_pair = if next.as_rule() == Rule::param_override {
        parameters = visit_param_override(next)?;

        children.next().ok_or(NetlistError::Internal(
            "instance missing name after parameters",
        ))?
    } else {
        next
    };

    if name_pair.as_rule() != Rule::ident {
        return Err(NetlistError::Internal("instance name was not an ident"));
    }

    let name = name_pair.as_str().to_string();

    let mut connections = HashMap::new();

    for child in children {
        if child.as_rule() == Rule::connection_list {
            connections = visit_connection_list(child)?;
        }
    }

    Ok(Instance {
        cell_type,
        name,
        connections,
        parameters,
    })
}

fn visit_param_override(pair: Pair<Rule>) -> Result<HashMap<String, Option<Expr>>, NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::param_override);

    let mut params = HashMap::new();

    for child in pair.into_inner() {
        if child.as_rule() == Rule::param_connection_list {
            for param in child.into_inner() {
                let named = param
                    .into_inner()
                    .next()
                    .ok_or(NetlistError::Internal("empty param connection"))?;

                if named.as_rule() != Rule::named_connection {
                    return Err(NetlistError::Internal("bad param connection"));
                }

                let (port, expr) = visit_named_connection(named)?;
                params.insert(port, expr);
            }
        }
    }

    Ok(params)
}

fn visit_connection_list(pair: Pair<Rule>) -> Result<HashMap<String, Option<Expr>>, NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::connection_list);

    let mut conns = HashMap::new();

    for conn in pair.into_inner() {
        if conn.as_rule() != Rule::connection {
            continue;
        }

        let inner = conn
            .into_inner()
            .next()
            .ok_or(NetlistError::Internal("empty connection"))?;

        match inner.as_rule() {
            Rule::named_connection => {
                let (port, expr) = visit_named_connection(inner)?;
                conns.insert(port, expr);
            }
            Rule::positional_connection => {
                return Err(NetlistError::UnsupportedPositionalConnection {
                    start: inner.as_span().start(),
                });
            }
            _ => {}
        }
    }

    Ok(conns)
}

fn visit_named_connection(pair: Pair<Rule>) -> Result<(String, Option<Expr>), NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::named_connection);

    let mut inner = pair.into_inner();

    let port = inner
        .next()
        .ok_or(NetlistError::Internal("named connection missing port"))?
        .as_str()
        .to_string();

    let expr = match inner.next() {
        Some(expr_pair) => Some(visit_expr(expr_pair)?),
        None => None,
    };

    Ok((port, expr))
}

fn visit_expr(pair: Pair<Rule>) -> Result<Expr, NetlistError> {
    match pair.as_rule() {
        Rule::expr => {
            let inner = pair
                .into_inner()
                .next()
                .ok_or(NetlistError::Internal("empty expr"))?;

            visit_expr(inner)
        }

        Rule::logic_expr => visit_logic_expr(pair),

        Rule::term => {
            let mut inner = pair.into_inner();

            let first = inner.next().ok_or(NetlistError::Internal("empty term"))?;

            match first.as_rule() {
                Rule::reject_concat => Err(NetlistError::UnsupportedConcat {
                    start: first.as_span().start(),
                }),

                Rule::reject_part_select => Err(NetlistError::UnsupportedPartSelect {
                    start: first.as_span().start(),
                }),

                Rule::bit_select => Ok(Expr::Net(parse_bit_select(first)?)),

                Rule::constant => Ok(Expr::Const(first.as_str().to_string())),

                Rule::ident => Ok(Expr::Net(first.as_str().to_string())),

                Rule::unaryop => {
                    let rhs_pair = inner
                        .next()
                        .ok_or(NetlistError::Internal("unary op missing rhs"))?;

                    Ok(Expr::Unary {
                        op: first.as_str().to_string(),
                        rhs: Box::new(visit_expr(rhs_pair)?),
                    })
                }

                Rule::logic_expr => visit_logic_expr(first),

                _ => Err(NetlistError::Internal("bad term")),
            }
        }

        Rule::reject_concat => Err(NetlistError::UnsupportedConcat {
            start: pair.as_span().start(),
        }),

        Rule::reject_part_select => Err(NetlistError::UnsupportedPartSelect {
            start: pair.as_span().start(),
        }),

        Rule::bit_select => Ok(Expr::Net(parse_bit_select(pair)?)),

        Rule::constant => Ok(Expr::Const(pair.as_str().to_string())),

        Rule::ident => Ok(Expr::Net(pair.as_str().to_string())),

        _ => Err(NetlistError::Internal("unexpected expr rule")),
    }
}

fn visit_logic_expr(pair: Pair<Rule>) -> Result<Expr, NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::logic_expr);

    let mut inner = pair.into_inner();

    let first = inner
        .next()
        .ok_or(NetlistError::Internal("logic expr missing first term"))?;

    let mut lhs = visit_expr(first)?;

    while let Some(op_pair) = inner.next() {
        let rhs_pair = inner
            .next()
            .ok_or(NetlistError::Internal("binary op missing rhs"))?;

        lhs = Expr::Binary {
            lhs: Box::new(lhs),
            op: op_pair.as_str().to_string(),
            rhs: Box::new(visit_expr(rhs_pair)?),
        };
    }

    Ok(lhs)
}

fn parse_bit_select(pair: Pair<Rule>) -> Result<String, NetlistError> {
    debug_assert_eq!(pair.as_rule(), Rule::bit_select);

    let mut inner = pair.into_inner();

    let name = inner
        .next()
        .ok_or(NetlistError::Internal("bit-select missing ident"))?
        .as_str()
        .to_string();

    let index = inner
        .next()
        .ok_or(NetlistError::Internal("bit-select missing index"))?
        .as_str()
        .to_string();

    Ok(format!("{name}[{index}]"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_basic_flattened_netlist() {
        let src = r#"
            module top(
                input [3:0] a,
                input b,
                output [1:0] y
            );

            wire [3:0] bus;
            wire n1;

            assign bus[0] = b;
            assign bus[1] = a[0];
            assign y[0] = bus[3];

            NAND2_X1 u1 (
                .A(a[2]),
                .B(bus[1]),
                .Y(n1)
            );

            endmodule
        "#;

        let netlist = parse_netlist(src).unwrap();

        assert_eq!(netlist.name, "top");

        assert_eq!(netlist.inputs, vec!["a[0]", "a[1]", "a[2]", "a[3]", "b"]);

        assert_eq!(netlist.outputs, vec!["y[0]", "y[1]"]);

        assert_eq!(
            netlist.wires,
            vec!["bus[0]", "bus[1]", "bus[2]", "bus[3]", "n1"]
        );

        assert_eq!(netlist.assignments.len(), 3);
        assert_eq!(
            netlist.assignments[0],
            Assign {
                lhs: Expr::Net("bus[0]".to_string()),
                rhs: Expr::Net("b".to_string()),
            }
        );

        assert_eq!(netlist.instances.len(), 1);
        let instance = netlist.instances.get("u1").unwrap();
        assert_eq!(instance.cell_type, "NAND2_X1");
        assert_eq!(instance.name, "u1");
    }

    #[test]
    fn rejects_part_select() {
        let src = r#"
            module top(input [3:0] a, output y);
                assign y = a[3:0];
            endmodule
        "#;

        let err = parse_netlist(src).unwrap_err();

        assert!(matches!(
            err,
            NetlistError::UnsupportedPartSelect { .. } | NetlistError::Parse(_)
        ));
    }

    #[test]
    fn rejects_concat() {
        let src = r#"
            module top(input a, input b, output y);
                assign y = {a, b};
            endmodule
        "#;

        let err = parse_netlist(src).unwrap_err();

        assert!(matches!(
            err,
            NetlistError::UnsupportedConcat { .. } | NetlistError::Parse(_)
        ));
    }
}
