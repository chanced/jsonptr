use super::*;

#[test]
fn test_from() {
    assert_eq!(Token::from("/").encoded(), "~1");
    assert_eq!(Token::from("~/").encoded(), "~0~1");
}
#[test]
fn test_from_encoded() {
    assert_eq!(Token::from_encoded("~1").encoded(), "~1");
    assert_eq!(Token::from_encoded("~0~1").encoded(), "~0~1");
}
