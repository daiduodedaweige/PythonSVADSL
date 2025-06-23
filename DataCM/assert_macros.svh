// assert macros.svh

`define state_transfer(label, clk, condition, result) \
    label: assert property (@(posedge clk) (condition) |->(result))

`define assert_with_result(label, clk, condition, result) \
    label: assert property (@(posedge clk) (condition) |->(result))

`define assert_without_result(label, clk, condition) \
    label: assert property (@(posedge clk) (condition))

`define assume_with_result(label, clk, condition, result) \
    label: assume property (@(posedge clk) (condition) |-> (result))

`define assume_without_result(label, clk, condition) \
    label: assume property (@(posedge clk) (condition))

`define cover(label, clk, condition) \
    label: cover property (@(posedge clk) (condition))
