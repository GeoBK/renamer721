#include "renamer.h"
uint64_t instruction_count=0;
void renamer::copy_map(uint64_t* source, uint64_t* destination)
{
    for(int i =0;i<lrf_size;i++)
    {
        destination[i]=source[i];
    }
}
renamer::renamer(uint64_t n_log_regs, uint64_t n_phys_regs, uint64_t n_branches)
{
    assert(n_phys_regs>n_log_regs);
    assert(n_branches>0 && n_branches<=64);

    lrf_size = n_log_regs;
    prf_size = n_phys_regs;
    unresolved_branch_limit = n_branches;
    al_size = prf_size - lrf_size;
    fl_size = prf_size - lrf_size;
    rmt = new uint64_t[n_log_regs];
    amt = new uint64_t[n_log_regs];
    prf = new uint64_t[prf_size];
    prf_bit_array = new bool[prf_size];
    for(int i=0;i<lrf_size;i++)
    {
        rmt[i]=i;
        amt[i]=i;
        prf_bit_array[i]=1;
    }
    freelist = new FreeList(fl_size,lrf_size);
    activelist = new ActiveList(al_size);
    checkpoints = new Checkpoint*[unresolved_branch_limit];
    for(int i =0;i<unresolved_branch_limit;i++){
        checkpoints[i]=new Checkpoint(lrf_size);
    }
    // printf("Done with construction of renamer!\n");
}

renamer::~renamer()
{
    delete[] rmt;
    delete[] amt;
    delete freelist;
    delete activelist;
    delete[] prf;
    delete[] prf_bit_array;
    delete[] checkpoints; 
}


bool renamer::stall_reg(uint64_t bundle_dst)
{
    if(freelist->get_freeregisters()>=bundle_dst)
    {
        return false;
    }
    else
    {
        return true;
    }
    
}

bool renamer::stall_branch(uint64_t bundle_branch)
{
    uint64_t free_branches=0; 
    // printf("Entering stall_branch\n");
    // printf("bundle_branches: %"PRIu64"\n",bundle_branch);
    // printf("GBM: %016llX\n",GBM);
    if(bundle_branch==0)
    {
        return false;
    }
    for(uint64_t i=0;i<unresolved_branch_limit;i++)
    {
        uint64_t mask = 1<<i;
        if((mask & GBM) == 0)
        {
            free_branches++;
            if(free_branches>=bundle_branch)
            {
                // printf("Done with stall_branch returning false!!\n");
                return false;
            }
              
        }
    }
     
    // printf("stall_branch returning true!!\n");
    return true;
}

uint64_t renamer::get_branch_mask()
{
    return GBM;
}

uint64_t renamer::rename_rsrc(uint64_t log_reg)
{
    return rmt[log_reg];
}

uint64_t renamer::rename_rdst(uint64_t log_reg)
{    
    
    // printf(", rename logical: %"PRIu64"\n",log_reg);
    // printf("free registers in freelist before assigning destination: %"PRIu64"\n",freelist->get_freeregisters());
    uint64_t phys_reg = freelist->pop();    
    prf_bit_array[phys_reg]=0;
    rmt[log_reg]=phys_reg;
    return rmt[log_reg];
}

uint64_t renamer::checkpoint()
{
    // printf("Inside checkpoint function\n");
    uint64_t branch_id = -1;
    uint64_t temp_debug = GBM;
    if(GBM>=(uint64_t)0x00FFFFFFFFFFFFFF)
    {
        printf("GBM inside checkpoint is %016llX\n",GBM);
    }
    //find free branch
    for(uint64_t i=0;i<unresolved_branch_limit;i++)
    {
        uint64_t mask = 1<<i;
        // printf("mask: %016llX\n",mask);
        // printf("mask& GBM: %016llX\n",mask & GBM);
        if((mask&GBM) == (uint64_t)0)
        {
            branch_id=i;
            GBM = GBM | mask;
            break;
        }
    }    
    // printf("Unresolved branch limit: %"PRIu64"\n",unresolved_branch_limit);
    
    if(branch_id==-1)
    {
        printf("GBM: %016llX\n",temp_debug);
    }
    assert(branch_id!=-1 && "No free branches, user must call stall_branch");
    // printf("BranchId: %"PRIu64"\n",branch_id);
    copy_map(rmt,checkpoints[branch_id]->smt);    
    checkpoints[branch_id]->fl_head_checkpoint=freelist->get_head();
    checkpoints[branch_id]->GBM_checkpoint = GBM;
    // printf("Done with checkpoint function\n");
    return branch_id;
}

bool renamer::stall_dispatch(uint64_t bundle_inst)
{
    if(activelist->get_free_entries()>=bundle_inst)
    {
        //printf("Stall dispatch false\n");
        return false;
    }
    else
    {
        // printf("Stall dispatch true\n");
        return true;
    }
    
}

uint64_t renamer::dispatch_inst(bool dest_valid,
	                       uint64_t log_reg,
	                       uint64_t phys_reg,
	                       bool load,
	                       bool store,
	                       bool branch,
	                       bool amo,
	                       bool csr,
	                       uint64_t PC)
{
    assert(!activelist->is_full() &&"Active list is full, user must check active list before calling dispatch");    
    // printf("Entering dispatch_instr\n");
    ALEntry rec;
    if(dest_valid)
    {        
        rec.lrn = log_reg;
        rec.prn = phys_reg;
    }
    rec.has_destination=dest_valid;
    rec.is_load=load;
    rec.is_store = store;
    rec.is_branch = branch;
    rec.is_amo = amo;
    rec.is_csr = csr;
    rec.pc = PC;
    rec.is_completed=false;
    rec.has_exception=false;
    rec.has_load_violation=false;
    rec.is_branch_mispredict=false;
    rec.is_value_mispredict=false;
    // printf("Done with instruction dispatch!!\n");
    return activelist->insert(rec);     
}

bool renamer::is_ready(uint64_t phys_reg)
{
    return prf_bit_array[phys_reg];
}

void renamer::clear_ready(uint64_t phys_reg)
{
    prf_bit_array[phys_reg]=0;
}

void renamer::set_ready(uint64_t phys_reg)
{
    prf_bit_array[phys_reg]=1;
}

uint64_t renamer::read(uint64_t phys_reg)
{
    //printf("Reading prf\n");
    return prf[phys_reg];
}

void renamer::write(uint64_t phys_reg, uint64_t value)
{
    prf[phys_reg]=value;    
}

void renamer::set_complete(uint64_t AL_index)
{
    // printf("set_complete called!!\n");
    activelist->set_complete(AL_index);
}

void renamer::resolve(uint64_t AL_index,
		     uint64_t branch_ID,
		     bool correct)
{
    // printf("Entering resolve function\n");
    uint64_t mask = 1<<branch_ID;
    
    if(correct)
    {    
        // printf("Correct prediction\n"); 
        // printf("Before masking GBM: %016llX\n",GBM);
        GBM=GBM^mask;
        // printf("After masking GBM: %016llX\n",GBM);
        for(int i=0; i< unresolved_branch_limit;i++)
        {
            if((checkpoints[i]->GBM_checkpoint&mask)!=0)
            {
                checkpoints[i]->GBM_checkpoint^=mask;
            }            
        }
    }
    else
    {
        // printf("Branch mispredicted\n"); 
        assert((GBM&mask)!=0);
        // printf("BranchId: %"PRIu64"\n",branch_ID);
        // printf("masking : %016llX\n",mask);
        GBM = checkpoints[branch_ID]->GBM_checkpoint;
        // printf("Before masking GBM: %016llX\n",GBM);
        GBM^=mask;
        // printf("After masking GBM: %016llX\n",GBM);
        //tail of active list, do we set the tail to after the branch instruction or before it?
        activelist->settail(AL_index+1);
        //head of freelist
        if(freelist->get_head()!=checkpoints[branch_ID]->fl_head_checkpoint)
        {
            freelist->set_notempty();
        }
        freelist->sethead(checkpoints[branch_ID]->fl_head_checkpoint);
        copy_map(checkpoints[branch_ID]->smt,rmt);
        
        
    } 
    // printf("Done with resolve function\n");   
}

bool renamer::precommit(bool &completed,
                       bool &exception, bool &load_viol, bool &br_misp, bool &val_misp,
	               bool &load, bool &store, bool &branch, bool &amo, bool &csr,
		       uint64_t &PC)
{
    //printf("Entering precommit function\n");
    ALEntry rec = activelist->peek();
    completed=rec.is_completed;
    exception=rec.has_exception;
    // if(rec.has_load_violation)
    // {
    //     printf("load violation at head of commit rec: %"PRIu64"\n",rec.pc);     
    // }
    load_viol=rec.has_load_violation;
    br_misp= rec.is_branch_mispredict;
    val_misp= rec.is_value_mispredict;
    load = rec.is_load;
    store = rec.is_store;
    branch = rec.is_branch;
    amo = rec.is_amo;
    csr = rec.is_csr;
    PC = rec.pc;
    bool ret_value = activelist->is_not_empty();
    // if(ret_value)
    // {
    //     printf("inside precommit with non empty queue");
    // }
    //printf("Done with precommit function!!\n");
    return ret_value;
}

void renamer::commit()
{
    // printf("Entering commit function\n");
    assert(activelist->is_not_empty());
    ALEntry rec = activelist->pop();
    if(rec.pc==0)
    {
        printf("rec: %"PRIu64"\n",rec.pc);        
    }
    
    assert(rec.is_completed && !rec.has_exception && !rec.has_load_violation);
    if(rec.has_destination)
    {
        // printf("lrn: %"PRIu64"\n",rec.lrn);
        uint64_t free_pr_entry = amt[rec.lrn];
        amt[rec.lrn]=rec.prn;
        freelist->push(free_pr_entry);
        // printf("rec.prn: %"PRIu64", rec.lrn: %"PRIu64"\n",rec.prn,rec.lrn);
        // printf("free registers in freelist after commiting: %"PRIu64"\n",freelist->get_freeregisters());
    }
    // printf("Done with commit function!!\n");
}

void renamer::squash()
{
    // printf("Starting squash function\n");
    //walk back through active list and add valid destinations into free_list
    //move tail in active list back to head
    //copy amt values into rmt
    activelist->clear();
    freelist->resetheadtotail();
    GBM=0;    
    copy_map(amt,rmt);  
    // printf("Exiting squash function!!\n");  
}

void renamer::set_exception(uint64_t AL_index)
{
    activelist->set_exception(AL_index);
}
void renamer::set_load_violation(uint64_t AL_index)
{
    // printf("Load violation at AL_index: %"PRIu64", al_head: %"PRIu64", al_tail: %"PRIu64"\n",AL_index,activelist->get_head(),activelist->get_tail());
    activelist->set_load_violation(AL_index);

    // activelist->settail(AL_index);
}
void renamer::set_branch_misprediction(uint64_t AL_index)
{
    activelist->set_branch_misprediction(AL_index);
}
void renamer::set_value_misprediction(uint64_t AL_index)
{
    activelist->set_value_misprediction(AL_index);
}

bool renamer::get_exception(uint64_t AL_index)
{
    activelist->get_exception(AL_index);
}