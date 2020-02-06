#include "renamer.h"

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
    for(int i=0;i<lrf_size;i++)
    {
        rmt[i]=i;
        amt[i]=i;
    }
    freelist = new FreeList(fl_size,lrf_size);
    activelist = new ActiveList(al_size);
    prf = new uint64_t[prf_size];
    prf_bit_array = new bool[prf_size];
    checkpoints = new Checkpoint*[unresolved_branch_limit];
    for(int i =0;i<unresolved_branch_limit;i++){
        checkpoints[i]=new Checkpoint(lrf_size);
    }
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
    uint64_t free_branches; 
    for(uint64_t i=0;i<unresolved_branch_limit;i++)
    {
        uint64_t mask = 1<<i;
        if(mask & GBM == 0)
        {
            free_branches++;
            if(free_branches>=bundle_branch)
            {
                return false;
            }            
        }
    }
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
    //TODO: Might need to add functionality here. ie return a new physical destination register from the free list and update the mappings in the RMT
    uint64_t phys_reg = freelist->pop();
    prf_bit_array[phys_reg]=0;
    rmt[log_reg]=phys_reg;
    return rmt[log_reg];
}

uint64_t renamer::checkpoint()
{
    uint64_t branch_id = -1;
    //find free branch
    for(uint64_t i=0;i<unresolved_branch_limit;i++)
    {
        uint64_t mask = 1<<i;
        if(mask & GBM == 0)
        {
            branch_id=i;
            GBM = GBM | mask;
            break;
        }
    }
    assert(branch_id!=-1 && "No free branches, user must call stall_branch");
    for(int i=0;i<fl_size;i++)
    {
        checkpoints[branch_id]->smt[i]=rmt[i];
    }
    checkpoints[branch_id]->fl_head_checkpoint=freelist->get_head();
    checkpoints[branch_id]->GBM_checkpoint = GBM;
    return branch_id;
}

bool renamer::stall_dispatch(uint64_t bundle_inst)
{
    if(activelist->get_free_entries()>=bundle_inst)
    {
        return false;
    }
    else
    {
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
    ALEntry rec;
    if(dest_valid)
    {
        rec.has_destination=true;
        rec.lrn = log_reg;
        rec.prn = phys_reg;
    }
    rec.is_load=load;
    rec.is_store = store;
    rec.is_branch = branch;
    rec.is_amo = amo;
    rec.is_csr = csr;
    rec.pc = PC;
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
    return prf[phys_reg];
}

void renamer::write(uint64_t phys_reg, uint64_t value)
{
    prf[phys_reg]=value;
}

void renamer::set_complete(uint64_t AL_index)
{
    activelist->set_complete(AL_index);
}

void renamer::resolve(uint64_t AL_index,
		     uint64_t branch_ID,
		     bool correct)
{
    uint64_t mask = 1<<branch_ID;
    if(correct)
    {        
        GBM=GBM^mask;
        for(int i=0; i< unresolved_branch_limit;i++)
        {
            checkpoints[i]->GBM_checkpoint^=mask;
        }
    }
    else
    {
        GBM = checkpoints[branch_ID]->GBM_checkpoint;
        GBM^=mask;
        //tail of active list, do we set the tail to after the branch instruction or before it?
        activelist->settail(AL_index);
        //head of freelist
        freelist->sethead(checkpoints[branch_ID]->fl_head_checkpoint);
        copy_map(checkpoints[branch_ID]->smt,rmt);
    }    
}

bool renamer::precommit(bool &completed,
                       bool &exception, bool &load_viol, bool &br_misp, bool &val_misp,
	               bool &load, bool &store, bool &branch, bool &amo, bool &csr,
		       uint64_t &PC)
{
    ALEntry rec = activelist->peek();
    completed=rec.is_completed;
    exception=rec.has_exception;
    load_viol=rec.has_load_violation;
    br_misp= rec.is_branch_mispredict;
    val_misp= rec.is_value_mispredict;
    load = rec.is_load;
    store = rec.is_store;
    branch = rec.is_branch;
    amo = rec.is_amo;
    csr = rec.is_csr;
    PC = rec.pc;
    return activelist->is_not_empty();
}

void renamer::commit()
{
    ALEntry rec = activelist->pop();
    assert(activelist->is_not_empty() && rec.is_completed && !rec.has_exception && !rec.has_load_violation);
    if(rec.has_destination)
    {
        uint64_t free_pr_entry = amt[rec.lrn];
        amt[rec.lrn]=rec.prn;
        freelist->push(free_pr_entry);
    }
}

void renamer::squash()
{
    //walk back through active list and add valid destinations into free_list
    //move tail in active list back to head
    //copy amt values into rmt
    activelist->clear();
    GBM=0; 
    for(int i =0;i<lrf_size;i++)
    {
        prf[i]=prf[amt[i]];
        prf_bit_array[i]=1;
        amt[i]=i;
    }
    freelist->reset();
    copy_map(amt,rmt);    
}

void renamer::set_exception(uint64_t AL_index)
{
    activelist->set_exception(AL_index);
}
void renamer::set_load_violation(uint64_t AL_index)
{
    activelist->set_load_violation(AL_index);
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