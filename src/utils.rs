use rustlogic::LogicNode;

pub fn flatten_cnf(expr:Box<LogicNode>) -> Vec<Box<LogicNode>>{
   let mut res:Vec<Box<LogicNode>> = vec![];

   let mut un_resolved:Vec<Box<LogicNode>> = vec![];
   un_resolved.push(expr);

   while !un_resolved.is_empty() {
       let cur_node = un_resolved.pop().unwrap();
       match *cur_node.clone(){
           LogicNode::And(l,r) => {
                un_resolved.push(l);
                un_resolved.push(r);
           },
           LogicNode::Or(_, _) => {
                res.push(cur_node);
           },
           LogicNode::Not(_) => {
               res.push(cur_node);
           },
           LogicNode::Variable(_) =>{
               res.push(cur_node);
           },
           _ => {
               unreachable!();
           }
       }
   }
   return res;
}

pub fn flatten_dnf(expr:Box<LogicNode>) -> Vec<Box<LogicNode>>{
   let mut res:Vec<Box<LogicNode>> = vec![];

   let mut un_resolved:Vec<Box<LogicNode>> = vec![];
   un_resolved.push(expr);

   while !un_resolved.is_empty() {
       let cur_node = un_resolved.pop().unwrap();
       match *cur_node.clone(){
           LogicNode::Or(l, r) => {
               un_resolved.push(l);
               un_resolved.push(r);
           },
           LogicNode::Not(_)|LogicNode::Variable(_) => {
               res.push(cur_node);
           },
           //
           // LogicNode::And(_,_) => {
           //     unreachable!();
           // },
           _ => {
               unreachable!();
           }
       }
   }
   return res;
}

pub fn optimize(expr:Box<LogicNode>) -> Box<LogicNode>{
    match *expr.clone() {
        LogicNode::And(left, rigt) => {
            if let LogicNode::True = *left{
                return rigt;
            }
            if let LogicNode::True = *rigt{
                return left;
            }
            let left_optimized = optimize(left);
            let rigt_optimized = optimize(rigt);
            return Box::new(LogicNode::And(left_optimized, rigt_optimized));
        }

        LogicNode::Or(left, rigt) => {
            if let LogicNode::False = *left{
                return rigt;
            }
            if let LogicNode::False = *rigt{
                return left;
            }
            let left_optimized = optimize(left);
            let rigt_optimized = optimize(rigt);
            return Box::new(LogicNode::Or(left_optimized, rigt_optimized));
        }

        _ => {
            return expr;
        }
    }
}
