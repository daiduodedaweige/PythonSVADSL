`include "assert_macros.svh"
module DataCtrlEntryStateChecker(
    input logic clock,
    input logic reset,
    input logic _GEN_23,
    input logic _GEN_24,
    input logic io_alloc_ready,
    input logic io_alloc_valid,
    input logic [3:0] io_clean_bits_hnTxnID,
    input logic io_clean_valid,
    input logic [3:0] io_cutHnTxnID_bits_before,
    input logic io_cutHnTxnID_valid,
    input logic [2:0] io_dcid,
    input logic [2:0] io_dsWriDB_bits_dcid,
    input logic io_dsWriDB_valid,
    input logic io_readToCHI_ready,
    input logic io_readToCHI_valid,
    input logic io_readToDB_ready,
    input logic io_readToDB_valid,
    input logic io_readToDS_ready,
    input logic io_readToDS_valid,
    input logic io_resp_ready,
    input logic io_resp_valid,
    input logic io_task_bits_dataOp_read,
    input logic io_task_bits_dataOp_repl,
    input logic io_task_bits_dataOp_save,
    input logic io_task_bits_dataOp_send,
    input logic io_task_bits_dataVec_0,
    input logic io_task_bits_dataVec_1,
    input logic [3:0] io_task_bits_hnTxnID,
    input logic io_task_valid,
    input logic [2:0] io_txDatFire_bits_dcid,
    input logic io_txDatFire_valid,
    input logic next_opBeat,
    input logic reg_dataVec_0,
    input logic reg_dataVec_1,
    input logic reg_opBeat,
    input logic [2:0] reg_state,
    input logic reg_task_dataOp_save,
    input logic reg_task_dataOp_send,
    input logic reg_task_dataVec_0,
    input logic reg_task_dataVec_1,
    input logic [3:0] reg_task_hnTxnID,
    input logic [1:0] reg_wRBeat,
    input logic [1:0] reg_wSBeat,
    input logic taskHit
);

    `state_transfer(
        assert_from_FREE_to_ALLOC,
        clock,
        ((reg_state == 3'h0) && ((io_alloc_valid) && (io_alloc_ready))),
        (reg_state == 3'h1)
    );
    `state_transfer(
        assert_from_ALLOC_to_REPL,
        clock,
        (((reg_state == 3'h1) && ((io_task_valid) && (io_task_bits_hnTxnID == reg_task_hnTxnID))) && (io_task_bits_dataOp_repl)),
        ((io_readToDS_valid) && (io_readToDB_valid))
    );
    `state_transfer(
        assert_from_ALLOC_to_READ,
        clock,
        ((((reg_state == 3'h1) && ((io_task_valid) && (io_task_bits_hnTxnID == reg_task_hnTxnID))) && (io_task_bits_dataOp_read)) && (!(io_task_bits_dataOp_repl))),
        (io_readToDB_valid)
    );
    `state_transfer(
        assert_from_ALLOC_to_SEND,
        clock,
        (((((reg_state == 3'h1) && ((io_task_valid) && (io_task_bits_hnTxnID == reg_task_hnTxnID))) && (io_task_bits_dataOp_send)) && (!(io_task_bits_dataOp_repl))) && (!(io_task_bits_dataOp_read))),
        (reg_state == 3'h4)
    );
    `state_transfer(
        assert_from_ALLOC_to_SAVE,
        clock,
        ((((((reg_state == 3'h1) && ((io_task_valid) && (io_task_bits_hnTxnID == reg_task_hnTxnID))) && (io_task_bits_dataOp_save)) && (!(io_task_bits_dataOp_repl))) && (!(io_task_bits_dataOp_read))) && (!(io_task_bits_dataOp_send))),
        (reg_state == 3'h5)
    );
    `state_transfer(
        assert_from_ALLOC_to_CLEAN,
        clock,
        ((((reg_state == 3'h1) && (!((io_task_valid) && (io_task_bits_hnTxnID == reg_task_hnTxnID)))) && (io_clean_valid)) && (io_clean_bits_hnTxnID == reg_task_hnTxnID)),
        (reg_state == 3'h7)
    );
    `state_transfer(
        assert_from_REPL_to_SEND,
        clock,
        (((reg_state == 3'h2) && ((io_readToDB_valid) && (io_readToDB_ready))) && ((((reg_task_dataVec_0) && (reg_task_dataVec_1)) && (reg_opBeat == 1'h1)) || ((!((reg_task_dataVec_0) && (reg_task_dataVec_1))) && (reg_opBeat == 1'h0)))),
        (reg_state == 3'h4)
    );
    `state_transfer(
        assert_from_READ_to_SEND,
        clock,
        ((((reg_state == 3'h3) && ((io_readToDB_valid) && (io_readToDB_ready))) && ((((reg_task_dataVec_0) && (reg_task_dataVec_1)) && (reg_opBeat == 1'h1)) || ((!((reg_task_dataVec_0) && (reg_task_dataVec_1))) && (reg_opBeat == 1'h0)))) && (reg_task_dataOp_send)),
        (reg_state == 3'h4)
    );
    `state_transfer(
        assert_from_READ_to_SAVE,
        clock,
        (((((reg_state == 3'h3) && ((io_readToDB_valid) && (io_readToDB_ready))) && ((((reg_task_dataVec_0) && (reg_task_dataVec_1)) && (reg_opBeat == 1'h1)) || ((!((reg_task_dataVec_0) && (reg_task_dataVec_1))) && (reg_opBeat == 1'h0)))) && (reg_task_dataOp_save)) && (!(reg_task_dataOp_send))),
        (reg_state == 3'h5)
    );
    `state_transfer(
        assert_from_READ_to_RESP,
        clock,
        (((((reg_state == 3'h3) && ((io_readToDB_valid) && (io_readToDB_ready))) && ((((reg_task_dataVec_0) && (reg_task_dataVec_1)) && (reg_opBeat == 1'h1)) || ((!((reg_task_dataVec_0) && (reg_task_dataVec_1))) && (reg_opBeat == 1'h0)))) && (!(reg_task_dataOp_save))) && (!(reg_task_dataOp_send))),
        (reg_state == 3'h6)
    );
    `state_transfer(
        assert_from_SEND_to_SAVE,
        clock,
        ((((reg_state == 3'h4) && ((io_readToCHI_valid) && (io_readToCHI_ready))) && ((((reg_task_dataVec_0) && (reg_task_dataVec_1)) && (reg_opBeat == 1'h1)) || ((!((reg_task_dataVec_0) && (reg_task_dataVec_1))) && (reg_opBeat == 1'h0)))) && (reg_task_dataOp_save)),
        (reg_state == 3'h5)
    );
    `state_transfer(
        assert_from_SEND_to_RESP,
        clock,
        ((((reg_state == 3'h4) && ((io_readToCHI_valid) && (io_readToCHI_ready))) && ((((reg_task_dataVec_0) && (reg_task_dataVec_1)) && (reg_opBeat == 1'h1)) || ((!((reg_task_dataVec_0) && (reg_task_dataVec_1))) && (reg_opBeat == 1'h0)))) && (!(reg_task_dataOp_save))),
        (reg_state == 3'h6)
    );
    `state_transfer(
        assert_from_SAVE_to_RESP,
        clock,
        (((reg_state == 3'h5) && ((io_readToDS_valid) && (io_readToDS_ready))) && ((((reg_task_dataVec_0) && (reg_task_dataVec_1)) && (reg_opBeat == 1'h1)) || ((!((reg_task_dataVec_0) && (reg_task_dataVec_1))) && (reg_opBeat == 1'h0)))),
        (reg_state == 3'h6)
    );
    `state_transfer(
        assert_from_RESP_to_ALLOC,
        clock,
        ((reg_state == 3'h6) && ((io_resp_valid) && (io_resp_ready))),
        (reg_state == 3'h1)
    );
    `state_transfer(
        assert_from_CLEAN_to_FREE,
        clock,
        ((reg_state == 3'h7) && (!((reg_dataVec_0) || (reg_dataVec_1)))),
        (reg_state == 3'h0)
    );
    `state_transfer(
        assert_from_CLEAN_to_ALLOC,
        clock,
        ((reg_state == 3'h7) && (!(!((reg_dataVec_0) || (reg_dataVec_1))))),
        (reg_state == 3'h1)
    );
    `assert_without_result(
        design_assert10,
        clock,
        (!((_GEN_24) && (!((_GEN_23) || (!(next_opBeat))))))
    );
    `assert_without_result(
        design_assert11,
        clock,
        (!((_GEN_24) && (!((!(_GEN_23)) || (next_opBeat)))))
    );
    `assert_without_result(
        design_assert12,
        clock,
        ((!(taskHit)) || (!(reg_opBeat)))
    );
    `assert_with_result(
        resp_valid,
        clock,
        (io_resp_valid),
        ((reg_wSBeat == 2'h0) && (reg_wRBeat == 2'h0))
    );
    `assume_without_result(
        assume1,
        clock,
        (io_task_bits_hnTxnID != $past(io_task_bits_hnTxnID))
    );
    `assume_with_result(
        assume2,
        clock,
        ((io_clean_valid) && (io_clean_bits_hnTxnID == reg_task_hnTxnID)),
        (reg_state == 3'h1)
    );
    `assume_with_result(
        assume3,
        clock,
        ((io_cutHnTxnID_valid) && (io_cutHnTxnID_bits_before == reg_task_hnTxnID)),
        (reg_state == 3'h1)
    );
    `assume_with_result(
        assume4,
        clock,
        (reg_state == 3'h2),
        (!(((io_readToDB_valid) && (io_readToDB_ready)) ^ ((io_readToDS_valid) && (io_readToDS_ready))))
    );
    `assume_with_result(
        assume8,
        clock,
        (taskHit),
        (reg_state == 3'h1)
    );
    `cover(
        datavec00,
        clock,
        ((io_task_bits_dataVec_0 == 1'h0) && (io_task_bits_dataVec_1 == 1'h0))
    );
    `cover(
        datavec01,
        clock,
        ((io_task_bits_dataVec_0 == 1'h1) && (io_task_bits_dataVec_1 == 1'h0))
    );
    `cover(
        datavec10,
        clock,
        ((io_task_bits_dataVec_0 == 1'h0) && (io_task_bits_dataVec_1 == 1'h1))
    );
    `cover(
        datavec11,
        clock,
        ((io_task_bits_dataVec_0 == 1'h1) && (io_task_bits_dataVec_1 == 1'h1))
    );


endmodule
