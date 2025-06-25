import sys
sys.path.append("/nfs/home/weijing/workspace/generateSVA")
from PySVADSL.env.sva_dsl import state_transfer, assert_Imp, assert_notImp, assume_Imp, assume_notImp, cover
from PySVADSL.env.sva_dsl import SVAExpr as sva
from PySVADSL.env.sva_utils import build_full_module_code, dump_verilog_exprs, save_to_file, include, generate_bind_statement
from enum import IntEnum
pkg = include("assert_macros.svh")
sva_code = ""
module = "DataCtrlEntryStateChecker"
clk = "clock"

# state
class STATE(IntEnum):
    FREE  = 0  # -> ALLOC
    ALLOC = 1
    REPL  = 2  # Read DS and DB at the same time to replace
    READ  = 3  # Read DS and save in DB
    SEND  = 4  # Read DB and send to CHI
    SAVE  = 5  # Read DB and send to DS
    RESP  = 6  # Send resp to Backend  // -> ALLOC
    CLEAN = 7  # Clean DB mask and DBIDPool


# signal
state = sva("reg_state", width=3)
allocfire = sva("io_alloc_valid") & sva("io_alloc_ready")
trepl = sva("io_task_bits_dataOp_repl")
tread = sva("io_task_bits_dataOp_read")
tsend = sva("io_task_bits_dataOp_send")
tsave = sva("io_task_bits_dataOp_save")
tvalid = sva("io_task_valid")
tid = sva("io_task_bits_hnTxnID",width=4)
rid = sva("reg_task_hnTxnID",width=4)
cvalid = sva("io_clean_valid")
cid = sva("io_clean_bits_hnTxnID",width=4)
tdbvalid = sva("io_readToDB_valid")
tdbready = sva("io_readToDB_ready")
tdbfire = tdbvalid & tdbready
rtsend = sva("reg_task_dataOp_send")
rtsave = sva("reg_task_dataOp_save")
iotrepl = sva("io_task_bits_dataOp_repl")
iotread = sva("io_task_bits_dataOp_read")
iotsend = sva("io_task_bits_dataOp_send")
iotsave = sva("io_task_bits_dataOp_save")
tchivalid = sva("io_readToCHI_valid") 
tchiready = sva("io_readToCHI_ready")
tchifire = tchivalid & tchiready
tdsvalid = sva("io_readToDS_valid")
tdsready = sva("io_readToDS_ready")
tdsfire = tdsvalid & tdsready
rspvalid = sva("io_resp_valid")
rspready = sva("io_resp_ready")
rspfire = rspvalid & rspready
cutidvalid = sva("io_cutHnTxnID_valid")
cutidbefore = sva("io_cutHnTxnID_bits_before",width=4)
tdfvalid = sva("io_txDatFire_valid") 
tdfdcid = sva("io_txDatFire_bits_dcid", width=3)
dcid = sva("io_dcid", width=3)
tdv0 = sva("io_task_bits_dataVec_0")
tdv1 = sva("io_task_bits_dataVec_1")
adv0 = sva("io_alloc_bits_dataVec_0")
adv1 = sva("io_alloc_bits_dataVec_1")

######################## state transfer basic

# FREE -> ALLOC
condition = (state == STATE.FREE) & allocfire
result = state == STATE.ALLOC
sva_code += state_transfer("assert_from_FREE_to_ALLOC", clk, condition, result)
# ALLOC -> REPL
thit = tvalid & (tid==rid)
condition = (state == STATE.ALLOC) & thit & trepl
result = tdsvalid & tdbvalid
sva_code += state_transfer("assert_from_ALLOC_to_REPL", clk, condition, result)
# ALLOC -> READ
condition = (state == STATE.ALLOC) & thit & tread & ~trepl
result = tdbvalid
sva_code += state_transfer("assert_from_ALLOC_to_READ", clk, condition, result)
# ALLOC -> SEND
condition = (state == STATE.ALLOC) & thit & tsend & ~trepl & ~tread
result = state == STATE.SEND
sva_code += state_transfer("assert_from_ALLOC_to_SEND", clk, condition, result)
# ALLOC -> SAVE
condition = (state == STATE.ALLOC) & thit & tsave & ~trepl & ~tread & ~tsend
result = state == STATE.SAVE
sva_code += state_transfer("assert_from_ALLOC_to_SAVE", clk, condition, result)
# ALLOC -> CLEAN
condition = (state == STATE.ALLOC) & ~thit & cvalid & (cid == rid) 
result = state == STATE.CLEAN
sva_code += state_transfer("assert_from_ALLOC_to_CLEAN", clk, condition, result)
# REPL -> SEND
fullsize = sva("reg_task_dataVec_0") & sva("reg_task_dataVec_1")
opb = sva("reg_opBeat")
willOpAll = (fullsize & (opb==1)) |  ~fullsize & (opb == 0)
condition = (state == STATE.REPL) & tdbfire & willOpAll
result = state == STATE.SEND
sva_code += state_transfer("assert_from_REPL_to_SEND", clk, condition, result)
# READ -> SEND
condition = (state == STATE.READ) & tdbfire & willOpAll & rtsend
result = state == STATE.SEND
sva_code += state_transfer("assert_from_READ_to_SEND", clk, condition, result)
# READ -> SAVE
condition = (state == STATE.READ) & tdbfire & willOpAll & rtsave & ~rtsend
result = state == STATE.SAVE
sva_code += state_transfer("assert_from_READ_to_SAVE", clk, condition, result)
# READ -> RESP
condition = (state == STATE.READ) & tdbfire & willOpAll & ~rtsave & ~rtsend
result = state == STATE.RESP
sva_code += state_transfer("assert_from_READ_to_RESP", clk, condition, result)
# SEND -> SAVE
condition = (state == STATE.SEND) & tchifire & willOpAll & rtsave
result = state == STATE.SAVE
sva_code += state_transfer("assert_from_SEND_to_SAVE", clk, condition, result)
# SEND -> RESP
condition = (state == STATE.SEND) & tchifire & willOpAll & ~rtsave
result = state == STATE.RESP
sva_code += state_transfer("assert_from_SEND_to_RESP", clk, condition, result)
# SAVE -> RESP
condition = (state == STATE.SAVE) & tdsfire & willOpAll
result = (state == STATE.RESP)
sva_code += state_transfer("assert_from_SAVE_to_RESP", clk, condition, result)
# RESP -> ALLOC
condition = (state == STATE.RESP) & rspfire
result = (state == STATE.ALLOC)
sva_code += state_transfer("assert_from_RESP_to_ALLOC", clk, condition, result)
# CLEAN -> FREE
isZero = ~ (sva("reg_dataVec_0") | sva("reg_dataVec_1"))
condition = (state == STATE.CLEAN) & isZero
result = (state == STATE.FREE)
sva_code += state_transfer("assert_from_CLEAN_to_FREE", clk, condition, result)
# CLEAN -> ALLOC
condition = (state == STATE.CLEAN) & ~isZero
result = (state == STATE.ALLOC)
sva_code += state_transfer("assert_from_CLEAN_to_ALLOC", clk, condition, result)




######################## design assert
wrb = sva("reg_wRBeat", width=2)
rsb = sva("reg_wSBeat", width=2)
dwdbhit = (state != STATE.FREE) & sva("io_dsWriDB_valid") & (sva("io_dsWriDB_bits_dcid", width=3) == dcid)
# Line 277: _GEN_24 & ~(_GEN_23 | ~next_opBeat)
# src/main/scala/dongjiang/data/DataCM.scala:205:19
temp1 = sva("_GEN_24")
temp2 = sva("_GEN_23")
temp3 = sva("next_opBeat")
condition = ~(temp1 & ~(temp2|~temp3))
sva_code += assert_notImp("design_assert10", clk, condition)
# Line 283: _GEN_24 & ~(~_GEN_23 | next_opBeat)
# // src/main/scala/dongjiang/data/DataCM.scala:206:19
condition = ~(temp1 & ~(~temp2|temp3))
sva_code += assert_notImp("design_assert11", clk, condition)
# Line 289: ~reset & ~(~taskHit | ~reg_opBeat)
# // src/main/scala/dongjiang/data/DataCM.scala:209:17
condition =  ~sva("taskHit") | ~opb
sva_code += assert_notImp("design_assert12", clk, condition)

######################## other assert
# resp valid only if waitall and sendall
condition =  rspvalid
result = (rsb == 0) & (wrb == 0)
sva_code += assert_Imp("resp_valid", clk, condition, result)

######################## assume
# hntxnid should not continual
condition =  tid != tid.past()
sva_code += assume_notImp("assume1", clk, condition)
# clean hit must alloc
condition = cvalid & (cid == rid) 
result = state == STATE.ALLOC
sva_code += assume_Imp("assume2", clk, condition, result)
# cutIdHit must alloc
condition = cutidvalid & (cutidbefore == rid)
result = state == STATE.ALLOC
sva_code += assume_Imp("assume3", clk, condition, result)
# replace task should readToDB and readToDS both high or both low
condition = state == STATE.REPL
result = ~(tdbfire ^ tdsfire)
sva_code += assume_Imp("assume4", clk, condition, result)
# taskhit must in alloc
condition = sva("taskHit") 
result = state == STATE.ALLOC
sva_code += assume_Imp("assume8", clk, condition, result)
# datavec should not be all zero
condition = adv0 | adv1
sva_code += assume_notImp("assume_alloc", clk, condition)


######################## cover
condition = (tdv0 == 1) & (tdv1 == 0)
sva_code += cover("datavec01", clk, condition)
condition = (tdv0 == 0) & (tdv1 == 1)
sva_code += cover("datavec10", clk, condition)
condition = (tdv0 == 1) & (tdv1 == 1)
sva_code += cover("datavec11", clk, condition)

######################## print code patern
full_code = build_full_module_code(module, pkg, clk, sva_code)
save_to_file("checker.sv", full_code)
dump_verilog_exprs()
print("✅ checker.sv 已生成")
