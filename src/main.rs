extern crate im_rc;
extern crate rpds;



fn main() {
    let s = String::new();
    let mut v1 = im_rc::Vector::new();
    v1.push_back(1);
    let v2 = rpds::Vector::new();
    let v2 = v2.push_back(1);
    println!("s = {} ", std::mem::size_of_val(&s));
    println!("im vec = {}", std::mem::size_of_val(&v1));
    println!("rpds vec = {}", std::mem::size_of_val(&v2));

    let l1 = rpds::List::new();
    let l1 = l1.push_front(String::new());
    println!("rpds list = {}", std::mem::size_of_val(&l1));

    let h1 = rpds::RedBlackTreeMap::new().insert(0, "zero").insert(1, "one");
    println!("rpds rbmap = {}", std::mem::size_of_val(&h1));

    use rpds::HashTrieMap;
    let h2 = HashTrieMap::new()
        .insert(1, "one")
        .insert(2, "two")
        .insert(3, "three");
    println!("rpds hmap = {}", std::mem::size_of_val(&h2));

    let h3 = im_rc::HashMap::new()
        .update(1, "one")
        .update(2, "two")
        .update(3, "three");
    println!("im hmap = {}", std::mem::size_of_val(&h3));

    let h4 = im_rc::OrdMap::new()
        .update(1, "one")
        .update(2, "two")
        .update(3, "three");
    println!("im ordmap = {}", std::mem::size_of_val(&h4));


}
