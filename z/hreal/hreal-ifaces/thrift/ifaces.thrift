struct Vertex {
    1: optional set<i32> ids,
    2: optional i32    intValue,
    3: optional bool   boolValue,
    4: optional double doubleValue,
    5: optional string stringValue
}

struct Response {
    1: optional map<i32, Vertex> result,
    2: optional string comment
}

service World {
    Response interpret(1:string code)
}

service CtrlZ {
    Response back(1:i32 steps)
}
