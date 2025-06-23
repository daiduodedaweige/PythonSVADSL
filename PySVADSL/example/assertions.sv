module cocotb(
    input logic clock,
    input logic reset,
    input logic io_alloc_ready,
    input logic io_alloc_valid,
    input logic io_fthInst_valid,
    input logic io_sdfsd,
    input logic stateReg_value
);

    `state_transfer(
        assert_from_FREE_to_FSTTASK,
        clock,
        ((stateReg_value=='h0) && ((io_alloc_valid) && (io_alloc_ready))),
        (io_fthInst_valid)
    );

endmodule
